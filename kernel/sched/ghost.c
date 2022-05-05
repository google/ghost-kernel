/*
 * Copyright 2021 Google LLC
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 */

#include <linux/syscalls.h>
#include <linux/mm.h>
#include <linux/anon_inodes.h>
#include <linux/bitmap.h>
#include <linux/bitops.h>
#include <linux/atomic.h>
#include <linux/kvm_host.h>
#include <uapi/linux/sched/types.h>
#include <linux/file.h>
#ifdef CONFIG_X86_64
#include <asm/apic.h>
#endif

#include <trace/events/sched.h>

#include "sched.h"
#include "kernfs-internal.h"

#define __INCLUDE_KERNEL_SCHED_GHOST
#include "ghost_uapi.h"
#include "ghost.h"

/* The ghost_txn pointer equals NULL or &enclave->cpu_data[this_cpu].txn */
static DEFINE_PER_CPU_READ_MOSTLY(struct ghost_txn *, ghost_txn);

/*
 * Use per-cpu memory instead of stack memory to avoid memsetting.  We only
 * send one message at a time per cpu.
 */
static DEFINE_PER_CPU(struct bpf_ghost_msg, bpf_ghost_msg);

struct ghost_sw_region {
	struct list_head list;			/* ghost_enclave glue */
	uint32_t alloc_scan_start;		/* allocator starts scan here */
	struct ghost_sw_region_header *header;  /* pointer to vmalloc memory */
	size_t mmap_sz;				/* size of mmapped region */
	struct ghost_enclave *enclave;
};

static void _ghost_task_new(struct rq *rq, struct task_struct *p,
			    bool runnable);
static void ghost_task_yield(struct rq *rq, struct task_struct *p);
static void ghost_task_blocked(struct rq *rq, struct task_struct *p);
static void task_deliver_msg_task_new(struct rq *rq, struct task_struct *p,
				      bool runnable);
static void task_deliver_msg_affinity_changed(struct rq *rq,
					      struct task_struct *p);
static bool task_deliver_msg_departed(struct rq *rq, struct task_struct *p);
static void task_deliver_msg_wakeup(struct rq *rq, struct task_struct *p);
static void task_deliver_msg_latched(struct rq *rq, struct task_struct *p,
				     bool latched_preempt);
static bool cpu_deliver_msg_tick(struct rq *rq);
static int task_target_cpu(struct task_struct *p);
static int agent_target_cpu(struct rq *rq);
static inline bool ghost_txn_ready(int cpu);
static inline void ghost_claim_and_kill_txn(int cpu, enum ghost_txn_state err);
static void ghost_commit_all_greedy_txns(void);
static void ghost_commit_pending_txn(int where);
static void release_from_ghost(struct rq *rq, struct task_struct *p);
static void ghost_wake_agent_on(int cpu);
static void ghost_wake_agent_of(struct task_struct *p);
static void ghost_latched_task_preempted(struct rq *rq);
static void ghost_task_preempted(struct rq *rq, struct task_struct *p);
static void _ghost_task_preempted(struct rq *rq, struct task_struct *p,
				  bool was_latched);

static void ghost_task_new(struct rq *rq, struct task_struct *p);

struct rq *move_queued_task(struct rq *rq, struct rq_flags *rf,
			    struct task_struct *p, int new_cpu);

static void __enclave_remove_task(struct ghost_enclave *e,
				  struct task_struct *p);
static int __sw_region_free(struct ghost_sw_region *region);
static const struct file_operations queue_fops;

static void ghost_destroy_enclave(struct ghost_enclave *e);
static void enclave_release(struct kref *k);

static inline gtid_t gtid(struct task_struct *p)
{
	return p->gtid;
}

/* True if X and Y have the same enclave, including having no enclave. */
static bool check_same_enclave(int cpu_x, int cpu_y)
{
	struct ghost_enclave *x, *y;

	if (WARN_ON_ONCE(cpu_x < 0 || cpu_y < 0
			 || cpu_x >= nr_cpu_ids || cpu_y >= nr_cpu_ids))
		return false;

	if (cpu_x == cpu_y)
		return true;

	rcu_read_lock();
	x = rcu_dereference(per_cpu(enclave, cpu_x));
	y = rcu_dereference(per_cpu(enclave, cpu_y));
	rcu_read_unlock();

	return x == y;
}

/* enclave::is_dying */
#define ENCLAVE_IS_DYING	(1U << 0)
#define ENCLAVE_IS_REAPABLE	(1U << 1)

static inline bool enclave_is_dying(struct ghost_enclave *e)
{
	lockdep_assert_held(&e->lock);

	return e->is_dying & ENCLAVE_IS_DYING;
}

static inline bool enclave_is_reapable(struct ghost_enclave *e)
{
	lockdep_assert_held(&e->lock);

	if (e->is_dying & ENCLAVE_IS_REAPABLE) {
		WARN_ON_ONCE(!enclave_is_dying(e));
		return true;
	}
	return false;
}

#ifdef CONFIG_BPF
#include <linux/filter.h>

static void ghost_bpf_pnt(struct ghost_enclave *e, struct rq *rq,
			  struct task_struct *prev, struct rq_flags *rf)
{
	struct task_struct *agent = rq->ghost.agent;
	struct bpf_ghost_sched_kern ctx[1];
	struct bpf_prog *prog;
	struct ghost_enclave *old_target;

	lockdep_assert_held(&rq->lock);

	rcu_read_lock();
	prog = rcu_dereference(e->bpf_pnt);
	if (!prog) {
		rcu_read_unlock();
		return;
	}
	/* Zero the struct to avoid leaking stack data in struct padding */
	memset(ctx, 0, sizeof(struct bpf_ghost_sched_kern));

	ctx->agent_on_rq = agent && agent->on_rq;
	ctx->agent_runnable = ctx->agent_on_rq && !rq->ghost.blocked_in_run;

	ctx->might_yield = rq_adj_nr_running(rq) > 0;
	ctx->dont_idle = false;

	if (rq->ghost.latched_task) {
		ctx->next_gtid = gtid(rq->ghost.latched_task);
	} else if (task_has_ghost_policy(prev)
		   && prev->state == TASK_RUNNING
		   && prev != agent
		   && !rq->ghost.must_resched) {
		ctx->next_gtid = gtid(prev);
	} else {
		ctx->next_gtid = 0;
	}

	/*
	 * BPF programs attached here may call ghost_run_gtid(), which requires
	 * that we not hold any RQ locks.  We are called from
	 * pick_next_task_ghost where it is safe to unlock the RQ.
	 */
	rq_unpin_lock(rq, rf);
	raw_spin_unlock(&rq->lock);

	old_target = set_target_enclave(e);
	rq->ghost.in_pnt_bpf = true;
	BPF_PROG_RUN(prog, ctx);
	rq->ghost.in_pnt_bpf = false;
	restore_target_enclave(old_target);

	raw_spin_lock(&rq->lock);
	rq_repin_lock(rq, rf);

	rcu_read_unlock();

	if (ctx->dont_idle) {
		/*
		 * The next time this rq selects the idle task, it will bail out
		 * of do_idle() quickly.  Since we unlocked the RQ lock, it's
		 * possible that this rq will pick something other than the idle
		 * task, which is fine.
		 */
		rq->ghost.dont_idle_once = true;
	}
}

/*
 * Returns true (default) if the user wants us to send the message.
 * Note that our caller holds an RQ lock, and we can't safely unlock it, so
 * programs at the attach point can't call ghost_run_gtid().
 */
static bool ghost_bpf_msg_send(struct ghost_enclave *e,
			       struct bpf_ghost_msg *msg)
{
	struct bpf_prog *prog;
	struct ghost_enclave *old_target;
	bool send;

	rcu_read_lock();
	prog = rcu_dereference(e->bpf_msg_send);
	if (!prog) {
		rcu_read_unlock();
		return true;
	}
	/* Program returns 0 if they want us to send the message. */
	old_target = set_target_enclave(e);
	send = BPF_PROG_RUN(prog, msg) == 0;
	restore_target_enclave(old_target);
	rcu_read_unlock();
	return send;
}
#else

static inline void ghost_bpf_pnt(struct ghost_enclave *e, struct rq *rq,
				 struct rq_flags *rf)
{
	return;
}

static inline bool ghost_bpf_msg_send(struct ghost_enclave *e,
				      struct bpf_ghost_msg *msg)
{
	return true;
}
#endif	/* CONFIG_BPF */

/*
 * There are certain things we can't do in the scheduler while holding rq locks
 * (or enclave locks, which are ordered after the rq lock), such as
 * schedule_work() (which grabs a scheduler lock internally), or even kref_put
 * an enclave, since enclave_release calls vfree, which grabs a lot of locks and
 * can't sleep.  It is safe to kref_put while holding locks if we know it's not
 * the last kref.
 *
 * We still need to schedule_work and drop refcounts, so we need another layer
 * of indirection: defer the schedule_work, which is itself a deferred work
 * mechanism.  The typical way to defer work from within the scheduler is to use
 * a balance_callback.  These can unlock and relock the RQ lock (and e->lock),
 * so we can schedule_work.
 *
 * Why not just do the work in balance_callback?  We still want to
 * schedule_work, since our worker may want to block or could take a long time.
 * balance_callbacks still run from within the scheduler, after all, so we
 * shouldn't block or take a long time.  task_reaper probably doesn't block, but
 * it may take a while, so it's better to run it from a workqueue.  vfree
 * (called from enclave_release) may sleep, so it needs to be called from a
 * workqueue.
 *
 * Notes:
 * - Typically you must hold both RQ and e locks to muck with enclave_work:
 *	- Hold both locks to enqueue/dequeue enclave_work
 *	- Hold the RQ lock to queue_balance_callback.
 *	- Hold the E lock to access any field in enclave_work
 * - You can schedule_work for e.g. task_reaper without using enclave_work.
 *   enclave_work is just a helper to schedule_work().
 * - The enclave_work can be submitted to at most one cpu's rq at a time.  But
 *   any cpu can come along and add work to it.
 * - What keeps the enclave, and thus the embedded enclave_work struct alive?
 *   krefs.  Whoever submits enclave_work passes along a kref.  In the case of
 *   running the task_reaper, this is done in submit_enclave_work.  In the case
 *   of decrefs, this is done implicitly: we are passing a bunch of references
 *   to be put later.
 * - It's highly unlikely that we'll ever have more than one enclave_work queued
 *   up on a cpu, since a cpu has at most one enclave at a time.
 * - enclave_release itself calls schedule_work.  It is possible for
 *   enclave_release to be called from some path other than enclave_work: from
 *   many other paths actually.  The balance_callback allows us to safely
 *   schedule_work, but not vfree.  So we can decref, and enclave_release
 *   schedules the actual freeing of the enclave.
 */

/*
 * The balance_callback.  rq is locked, but we can temporarily unlock it.  We
 * are not preemptible.  It's safe to do a raw_spin_unlock, just like
 * double_lock_balance().
 */
static void __do_enclave_work(struct rq *rq)
{
	struct enclave_work *ew;
	struct ghost_enclave *e;
	unsigned long irq_fl;
	bool run_task_reaper;
	unsigned int nr_decrefs;

	while ((ew = list_first_entry_or_null(&rq->ghost.enclave_work,
					      struct enclave_work, link))) {
		e = container_of(ew, struct ghost_enclave, ew);
		spin_lock_irqsave(&e->lock, irq_fl);

		list_del_init(&ew->link);

		run_task_reaper = ew->run_task_reaper;
		ew->run_task_reaper = false;
		nr_decrefs = ew->nr_decrefs;
		ew->nr_decrefs = 0;

		spin_unlock_irqrestore(&e->lock, irq_fl);
		/*
		 * At this point, all that keeps e alive is the krefs passed
		 * with ew.
		 */

		raw_spin_unlock(&rq->lock);

		if (run_task_reaper) {
			/*
			 * Whoever set run_task_reaper increffed.  This is
			 * passed to task_reaper.  In theory, rq and task_reaper
			 * could be on another cpu, and it could run and decref.
			 * That could be the last ref on e.  This is fine - we
			 * only touch e if we have more krefs still.
			 */
			if (!schedule_work(&e->task_reaper))
				kref_put(&e->kref, enclave_release);
		}
		for (; nr_decrefs > 0; nr_decrefs--)
			kref_put(&e->kref, enclave_release);

		raw_spin_lock(&rq->lock);
	}
}

static void submit_enclave_work(struct ghost_enclave *e, struct rq *rq,
				bool run_task_reaper, int nr_decrefs)
{
	struct enclave_work *ew = &e->ew;
	bool need_work = false;

	VM_BUG_ON(nr_decrefs < 0);
	WARN_ON_ONCE(run_task_reaper && !enclave_is_reapable(e));

	lockdep_assert_held(&rq->lock);
	lockdep_assert_held(&e->lock);

	if (run_task_reaper && !ew->run_task_reaper) {
		kref_get(&e->kref);
		ew->run_task_reaper = true;
		need_work = true;
	}
	if (nr_decrefs) {
		ew->nr_decrefs += nr_decrefs;
		need_work = true;
	}
	if (!need_work) {
		/*
		 * Note that if we have added no work, then we've added no
		 * krefs, and cannot submit ew to the rq's enclave_work list.
		 */
		return;
	}
	if (!list_empty(&ew->link)) {
		/* Already queued on some rq, but maybe not this one! */
		return;
	}
	list_add(&ew->link, &rq->ghost.enclave_work);
	/* OK to resubmit ew_head, so long as the func stays the same */
	queue_balance_callback(rq, &rq->ghost.ew_head, __do_enclave_work);
}

static inline bool on_ghost_rq(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(rq != task_rq(p));
	return !list_empty(&p->ghost.run_list);
}

static inline bool ghost_can_schedule(struct rq *rq, gtid_t gtid)
{
	const struct sched_class *class = rq->curr->sched_class;

	lockdep_assert_held(&rq->lock);
	if (ghost_class(class) || class == &idle_sched_class)
		return true;

	/* agent is always allowed to preempt */
	if (gtid == GHOST_AGENT_GTID)
		return true;

	/* A higher priority task is running, must wait to schedule ghost. */
	return false;
}

static inline void task_barrier_inc(struct rq *rq, struct task_struct *p)
{
	struct ghost_status_word *sw;

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(rq != task_rq(p));

	sw = p->ghost.status_word;
	/*
	 * Order any SW flag changes before the barrier, even though the barrier
	 * is primarily used for making sure we don't miss messages.
	 */
	smp_store_release(&sw->barrier, sw->barrier + 1);
}

static inline void agent_barrier_inc(struct rq *rq)
{
	struct ghost_status_word *sw = rq->ghost.agent->ghost.status_word;
	uint32_t b;

	lockdep_assert_held(&rq->lock);

	/* We may clobber a lockless increment. See pick_agent() for details. */
	b = READ_ONCE(rq->ghost.agent_barrier) + 1;
	WRITE_ONCE(rq->ghost.agent_barrier, b);
	sw->barrier = b;
}

static inline uint32_t task_barrier_get(struct task_struct *p)
{
	struct rq *rq = task_rq(p);

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(is_agent(rq, p));
	VM_BUG_ON(!p->ghost.status_word);

	return p->ghost.status_word->barrier;
}

static inline uint32_t agent_barrier_get(struct task_struct *agent)
{
	struct ghost_status_word *sw = agent->ghost.status_word;
	struct rq *rq = task_rq(agent);

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(!is_agent(rq, agent));
	VM_BUG_ON(!agent->ghost.status_word);

	sw->barrier = READ_ONCE(rq->ghost.agent_barrier);
	return sw->barrier;
}

static inline uint32_t barrier_get(struct task_struct *p)
{
	if (p->ghost.agent)
		return agent_barrier_get(p);
	return task_barrier_get(p);
}

static inline void invalidate_cached_tasks(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);

	if (unlikely(rq->ghost.latched_task == p)) {
		if (rq->ghost.skip_latched_preemption) {
			/*
			 * We cannot produce a TASK_PREEMPT msg here.
			 *
			 * This is called via ghost_move_task() during txn
			 * commit after validating the task to be committed.
			 * Thus if we produce a TASK_PREEMPT msg it won't be
			 * caught by the task->barrier and prevent the txn
			 * from committing.
			 *
			 * Then it is possible to observe back-to-back
			 * TASK_PREEMPT msgs in the agent (the second
			 * would be due to a real preemption) which will
			 * trigger a 'task->preempted' CHECK-fail in the agent.
			 */
			rq->ghost.latched_task = NULL;
		} else {
			/*
			 * This is called via non-ghost move_queued_task()
			 * callers (e.g. sched_setaffinity). We produce a
			 * TASK_PREEMPT msg to let the agent know that the
			 * task is no longer latched (without this the task
			 * would be stranded).
			 */
			ghost_latched_task_preempted(rq);
		}
	}

	rq->ghost.skip_latched_preemption = false;
}

static inline bool is_cached_task(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);

	return rq->ghost.latched_task == p;
}

static inline void schedule_next(struct rq *rq, gtid_t gtid, bool resched)
{
	lockdep_assert_held(&rq->lock);

	VM_BUG_ON(gtid != GHOST_NULL_GTID && gtid != GHOST_AGENT_GTID);

	/*
	 * If a task running on a non-ghost CPU switches into ghost then
	 * this function is called via set_next_task_ghost() but without
	 * an agent associated with 'rq'.
	 *
	 * Regardless we still need to do resched_curr() so resist the
	 * temptation to do an early return.
	 */
	if (unlikely(!rq->ghost.agent))
		goto done;

	if (gtid == GHOST_AGENT_GTID) {
		/*
		 * Increment barrier to guarantee that a concurrent ghost_run()
		 * doesn't "lose" this schedule-to-agent edge. In other words
		 * we want that ghost_run() to return -ESTALE.
		 */
		agent_barrier_inc(rq);
		rq->ghost.blocked_in_run = false;
	} else if (gtid == GHOST_NULL_GTID) {
		rq->ghost.must_resched = true;
	}

done:
	if (resched && ghost_can_schedule(rq, gtid))
		resched_curr(rq);
}

static inline void schedule_agent(struct rq *rq, bool resched)
{
	schedule_next(rq, GHOST_AGENT_GTID, resched);
}

static inline void _force_offcpu(struct rq *rq, bool resched,
				 bool ignore_prev_preemption)
{
	VM_BUG_ON(!ghost_class(rq->curr->sched_class));

	rq->ghost.ignore_prev_preemption = ignore_prev_preemption;

	schedule_next(rq, GHOST_NULL_GTID, resched);
}

static inline void force_offcpu(struct rq *rq, bool resched)
{
	_force_offcpu(rq, resched, /*ignore_prev_preemption=*/false);
}

static void __update_curr_ghost(struct rq *rq, bool update_sw)
{
	struct task_struct *curr = rq->curr;
	struct ghost_status_word *sw = curr->ghost.status_word;
	u64 delta, now;

	/*
	 * Bail if this due to a "spurious" dequeue.
	 *
	 * For e.g. _dequeue_task_ghost() is called when scheduling properties
	 * of a runnable ghost task change (e.g. nice or cpu affinity), but
	 * if that task is not oncpu then nothing needs to be done here.
	 */
	if (!ghost_class(curr->sched_class))
		return;

	VM_BUG_ON(!curr->se.exec_start);

	now = rq_clock_task(rq);
	delta = now - curr->se.exec_start;
	if ((s64)delta > 0) {
		curr->se.sum_exec_runtime += delta;
		account_group_exec_runtime(curr, delta);
		cgroup_account_cputime(curr, delta);
		curr->se.exec_start = now;
	}

	if (update_sw)
		WRITE_ONCE(sw->runtime, curr->se.sum_exec_runtime);
}

static void _update_curr_ghost(struct rq *rq)
{
	__update_curr_ghost(rq, true);
}

static void _prio_changed_ghost(struct rq *rq, struct task_struct *p, int old)
{
	/*
	 * XXX produce MSG_TASK_PRIO_CHANGE into p->ghost.dst_q.
	 */
	ghost_wake_agent_of(p);

	/*
	 * Note that if a running task changes priority then
	 * __sched_setscheduler -> set_next_task_ghost guarantees
	 * a switch to the local agent.
	 */
}

static void _switched_to_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_status_word *status_word = p->ghost.status_word;

	if (task_running(rq, p)) {
		ghost_sw_set_time(status_word, ktime_get_ns());
		ghost_sw_set_flag(status_word, GHOST_SW_TASK_ONCPU);
	}

	if (task_on_rq_queued(p))
		ghost_sw_set_flag(status_word, GHOST_SW_TASK_RUNNABLE);

	WRITE_ONCE(status_word->runtime, p->se.sum_exec_runtime);

	if (is_agent(rq, p) || !task_running(rq, p)) {
		ghost_task_new(rq, p);
		ghost_wake_agent_of(p);    /* no-op if 'p' is an agent */
	} else {
		/*
		 * Wait for an oncpu task to schedule before advertising
		 * it to the agent. There isn't much the agent can do as
		 * long as the task is oncpu anyways.
		 *
		 * Note that if a running task switches into ghost then
		 * __sched_setscheduler -> set_next_task_ghost guarantees
		 * a context switch to the local agent at the earliest
		 * possible opportunity.
		 */
		VM_BUG_ON(p->ghost.new_task);
		p->ghost.new_task = true;  /* see ghost_prepare_task_switch() */
	}
}

static void _switched_from_ghost(struct rq *rq, struct task_struct *p)
{
	/*
	 * A running task can be switched into ghost while it is executing
	 * sched_setscheduler(cfs). Make sure TASK_NEW is produced before
	 * TASK_DEPARTED in this case.
	 *
	 * Note that unlike TASK_AFFINITY_CHANGED (which we just forget in
	 * a similar situation) we must produce TASK_DEPARTED so the task's
	 * status_word is freed by the agent.
	 *
	 * Also note that we must call ghost_task_new() here before calling
	 * release_from_ghost() since the former sets things up for the
	 * latter to tear down (e.g. adding task to enclave->task_list).
	 */
	if (unlikely(p->ghost.new_task)) {
		WARN_ON_ONCE(!task_current(rq, p));
		p->ghost.new_task = false;
		/*
		 * Task is departing from ghost so don't advertise it as
		 * runnable otherwise the agent could try to schedule it
		 * before it sees TASK_DEPARTED (in this case the commit
		 * fails with GHOST_TXN_INVALID_TARGET which is treated as
		 * a fatal error by the agent).
		 */
		_ghost_task_new(rq, p, /*runnable=*/false);
		ghost_wake_agent_of(p);
	}

	release_from_ghost(rq, p);

	/*
	 * Mark end of the switchto chain (if any) since the oncpu task
	 * is no longer being scheduled by ghost.
	 */
	if (task_current(rq, p)) {
		WARN_ON_ONCE(rq->ghost.switchto_count < 0);
		rq->ghost.switchto_count = 0;
	}
}

static void _dequeue_task_ghost(struct rq *rq, struct task_struct *p, int flags)
{
	const bool spurious = flags & DEQUEUE_SAVE;
	const bool sleeping = flags & DEQUEUE_SLEEP;
	struct ghost_status_word *sw = p->ghost.status_word;

	/*
	 * A task is accumulating cputime only when it is oncpu. Thus it is
	 * useless to call _update_curr_ghost for a task that is 'on_rq' but
	 * is not running (in this case we'll just update the cputime of
	 * whatever task happens to be oncpu).
	 *
	 * Ordinarily we wouldn't care but we routinely _dequeue_task_ghost()
	 * when migrating a task via ghost_move_task() during txn commit so
	 * we call _update_curr_ghost() only if 'p' is actually running.
	 */
	if (task_current(rq, p))
		_update_curr_ghost(rq);

	BUG_ON(rq->ghost.ghost_nr_running <= 0);
	rq->ghost.ghost_nr_running--;
	sub_nr_running(rq, 1);

	WARN_ON_ONCE(!on_ghost_rq(rq, p));
	list_del_init(&p->ghost.run_list);

	/*
	 * Clear the remotely latched task when it is dequeued (but only if
	 * it isn't spurious). Although unlikely this can happen via the
	 * ghost_run()->move_queued_task() code path.
	 */
	if (!spurious)
		invalidate_cached_tasks(rq, p);

	if (sleeping) {
		WARN_ON_ONCE(!(sw->flags & GHOST_SW_TASK_RUNNABLE));
		ghost_sw_clear_flag(sw, GHOST_SW_TASK_RUNNABLE);
	}

	if (is_agent(rq, p)) {
		WARN_ON_ONCE(rq->ghost.blocked_in_run && !spurious);
		return;
	}

	if (sleeping) {
		WARN_ON_ONCE(p->ghost.blocked_task);
		p->ghost.blocked_task = true;

		/*
		 * Return to local agent if it has expressed interest in
		 * this edge.
		 *
		 * We don't need the full resched_curr() functionality here
		 * because this must be followed by pick_next_task().
		 */
		if (rq->ghost.run_flags & RTLA_ON_BLOCKED)
			schedule_agent(rq, false);
	}
}

static void _put_prev_task_ghost(struct rq *rq, struct task_struct *p)
{
	_update_curr_ghost(rq);
}

static void
_enqueue_task_ghost(struct rq *rq, struct task_struct *p, int flags)
{
	add_nr_running(rq, 1);
	rq->ghost.ghost_nr_running++;

	WARN_ON_ONCE(on_ghost_rq(rq, p));
	list_add_tail(&p->ghost.run_list, &rq->ghost.tasks);
	p->ghost.last_runnable_at = ktime_get();

	if (flags & ENQUEUE_WAKEUP) {
		WARN_ON_ONCE(is_agent(rq, p) && rq->ghost.blocked_in_run);
	}
}

static void _set_next_task_ghost(struct rq *rq, struct task_struct *p,
				bool first)
{
	WARN_ON_ONCE(first);

	p->se.exec_start = rq_clock_task(rq);

	if (is_agent(rq, p))
		return;

	/*
	 * This can happen when a running task switches into ghost on a cpu
	 * without an agent (not common).
	 */
	if (unlikely(!rq->ghost.agent)) {
		force_offcpu(rq, true);
		return;
	}

	/*
	 * set_curr_task() is called when scheduling properties of a running
	 * task change (e.g. affinity, priority, sched_class etc). Get this
	 * task offcpu so the agent can incorporate these changes into its
	 * scheduling policy. Note that schedule_agent() below achieves two
	 * things:
	 * 1. get 'rq->curr' offcpu.
	 * 2. produce TASK_PREEMPTED so the agent knows 'rq->curr' got offcpu.
	 *
	 * The assumption behind return-to-local-agent is that changes to these
	 * properties are advertised via messages (e.g. TASK_AFFINITY etc).
	 *
	 * (another approach might be to produce a TASK_CHANGED msg here and
	 *  let the agent figure out exactly what changed).
	 */
	schedule_agent(rq, true);
}

/*
 * Called from the scheduler tick handler.  Returns true if everything is OK,
 * false if someone has been runnable but not scheduled for more than
 * e->max_unscheduled.
 *
 * Enclave and RQ are *unlocked*.
 */
static bool check_runnable_timeout(struct ghost_enclave *e, struct rq *rq)
{
	struct task_struct *p;
	struct rq_flags rf;
	ktime_t timeout;
	bool ok = true;

	timeout = READ_ONCE(e->max_unscheduled);

	if (!timeout)
		return ok;

	rq_lock_irqsave(rq, &rf);

	/*
	 * The ghost.tasks list is sorted; earliest non-zero runnable time
	 * first.
	 */
	list_for_each_entry(p, &rq->ghost.tasks, ghost.run_list) {
		if (is_agent(rq, p))
			continue;
		if (!p->ghost.last_runnable_at)
			continue;
		if (ktime_before(ktime_add_safe(p->ghost.last_runnable_at,
						timeout),
				 ktime_get())) {
			pr_info("enclave violation: enclave_%lu failed to run pid %u for over %lums\n",
				e->id, p->pid, ktime_to_ms(timeout));
			ok = false;
		}

		break;
	}
	rq_unlock_irqrestore(rq, &rf);

	return ok;
}

static void tick_handler(struct ghost_enclave *e, struct rq *rq)
{
	if (READ_ONCE(e->commit_at_tick))
		ghost_commit_all_greedy_txns();
	if (!check_runnable_timeout(e, rq))
		ghost_destroy_enclave(e);
}

static void _task_tick_ghost(struct rq *rq, struct task_struct *p, int queued)
{
	struct task_struct *agent = rq->ghost.agent;

	/*
	 * This can happen if a running task enters ghost on a CPU that
	 * is not associated with an agent but a timer interrupt sneaks
	 * in before we get the task offcpu.
	 */
	if (unlikely(!agent))
		return;

	if (agent == p) {
		/*
		 * We're currently running a ghost agent while a task is
		 * latched on the cpu. Normally, pick_next_ghost_agent()
		 * would have preempted the latched task, except in the
		 * case that DEFER_LATCHED_PREEMPTION_BY_AGENT is set. We need
		 * to prevent the latched task from experiencing an unbounded
		 * scheduling blackout if the agent runs for a while, so we
		 * preempt here in the tick handler.
		 *
		 * We could also hit this case without preemption deferment
		 * if a task was latched while the remote agent was running,
		 * and the tick hits before the remote agent reschedules.
		 * In that case, it is fine to preempt here instead of in
		 * the pick path.
		 *
		 * Note that the preemption edge in the pick path is not a new
		 * edge introduced by DEFER_LATCHED_PREEMPTION_BY_AGENT. Ie.
		 * previously when an agent is running with a ghost task
		 * latched, any trip through schedule() would trigger a latched
		 * preemption via pick_next_ghost_agent().
		 */
		if (rq->ghost.latched_task)
			ghost_latched_task_preempted(rq);
	}

	__update_curr_ghost(rq, false);

	if (cpu_deliver_msg_tick(rq))
		ghost_wake_agent_on(agent_target_cpu(rq));
}

static int _balance_ghost(struct rq *rq, struct task_struct *prev,
			  struct rq_flags *rf)
{

	struct task_struct *agent = rq->ghost.agent;

	if (!agent || !agent->on_rq)
		return 0;

	/*
	 * Try to commit a ready txn iff:
	 * - there is no higher priority runnable task.
	 * - there is no 'latched_task'
	 */
	if (!rq->ghost.latched_task && !rq_adj_nr_running(rq) &&
	    ghost_txn_ready(cpu_of(rq))) {
		rq_unpin_lock(rq, rf);
		raw_spin_unlock(&rq->lock);

		ghost_commit_pending_txn(COMMIT_AT_SCHEDULE);

		raw_spin_lock(&rq->lock);
		rq_repin_lock(rq, rf);
	}

	/*
	 * We have something to run in 'latched_task' or a higher priority
	 * sched_class became runnable while the rq->lock was dropped.
	 */
	return rq->ghost.latched_task || rq_adj_nr_running(rq);
}

static int _select_task_rq_ghost(struct task_struct *p, int cpu, int wake_flags)
{
	int waker_cpu = smp_processor_id();

	/* For anything but wake ups, just return the task_cpu */
	if (!(wake_flags & (WF_TTWU | WF_FORK)))
		return task_cpu(p);

	/*
	 * We have at least a couple of obvious choices here:
	 *
	 * 1. Keep the task on the same CPU it last ran on:
	 *    This is good because it doesn't migrate the task unbeknownst
	 *    to the agent but on the flip side we pay the cost of an IPI
	 *    if the waking CPU is different than task_cpu(p).
	 *
	 * 2. Migrate the task to the waking CPU:
	 *    This is good because we don't need an IPI to do the wakeup
	 *    but on the flip side this may end up being a pessimistic
	 *    choice when the agent actually schedules the task.
	 *
	 *    For e.g. if the waking cpu is in a different NUMA domain
	 *    than where the agent later schedules the task then we'll
	 *    pay the cost of task_rq_lock() across sockets which is
	 *    exactly what ttwu_queue_remote() aims to minimize.
	 *
	 * This can be configured using 'p->ghost.enclave->wake_on_waker_cpu'
	 * and the default is to keep the task on the same CPU it last ran on.
	 */
	if (READ_ONCE(p->ghost.enclave->wake_on_waker_cpu))
		p->ghost.twi.wake_up_cpu = waker_cpu;
	else
		p->ghost.twi.wake_up_cpu = task_cpu(p);

	p->ghost.twi.waker_cpu = waker_cpu;
	p->ghost.twi.last_ran_cpu = task_cpu(p);

	return p->ghost.twi.wake_up_cpu;
}

static inline bool task_is_dead(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);

	VM_BUG_ON(!task_has_ghost_policy(p));

	/*
	 * A ghost task always has a valid 'status_word' when it is alive
	 * so use that as a proxy to detect a dead task.
	 */
	return p->ghost.status_word == NULL;
}

static void set_txn_state(int *ptr, enum ghost_txn_state val)
{
	if (ptr)
		*ptr = val;
}

static int validate_next_task(struct rq *rq, struct task_struct *next,
			      uint32_t task_barrier, int *state)
{
	lockdep_assert_held(&rq->lock);

	if (next->ghost.agent) {
		set_txn_state(state, GHOST_TXN_INVALID_TARGET);
		return -EINVAL;
	}

	/*
	 * Task departed, but the agent hasn't yet processed the
	 * TASK_DEPARTED message.
	 */
	if (next->inhibit_task_msgs) {
		set_txn_state(state, GHOST_TXN_TARGET_STALE);
		return -EINVAL;
	}

	if (!task_has_ghost_policy(next)) {
		set_txn_state(state, GHOST_TXN_INVALID_TARGET);
		return -EINVAL;
	}

	/*
	 * ghost_run raced with task exit such that find_task_by_pid() was
	 * able to find the task but it was dead by the time task_rq_lock()
	 * returned. The most likely scenario is that agent hasn't seen the
	 * TASK_DEAD msg so treat this as a stale barrier.
	 */
	if (unlikely(task_is_dead(rq, next))) {
		set_txn_state(state, GHOST_TXN_TARGET_STALE);
		return -ESTALE;
	}

	if (unlikely(task_barrier_get(next) != task_barrier)) {
		set_txn_state(state, GHOST_TXN_TARGET_STALE);
		return -ESTALE;
	}

	if (!task_on_rq_queued(next)) {
		set_txn_state(state, GHOST_TXN_TARGET_NOT_RUNNABLE);
		return -EINVAL;
	}

	return 0;
}

static int validate_next_offcpu(struct rq *rq, struct task_struct *next,
				int *state)
{
	lockdep_assert_held(&rq->lock);

	if (next && task_running(rq, next)) {
		/*
		 * An agent must have attempted to preempt 'next' prior
		 * to scheduling it. But its possible that 'next' hasn't
		 * vacated its CPU yet.
		 */
		set_txn_state(state, GHOST_TXN_TARGET_ONCPU);
		return -EAGAIN;
	}

	return 0;
}

static inline struct task_struct *pick_agent(struct rq *rq)
{
	struct task_struct *agent = rq->ghost.agent;
	struct task_struct *next = NULL;

	BUG_ON(!agent || !agent->on_rq || !on_ghost_rq(rq, agent));

	/*
	 * 'agent' is on_rq so 'ghost_nr_running' must be at least 1.
	 */
	BUG_ON(rq->ghost.ghost_nr_running < 1);

	if (READ_ONCE(rq->ghost.agent_should_wake)) {
		WRITE_ONCE(rq->ghost.agent_should_wake, false);
		/*
		 * Preemptively sync the agent_barrier, since we know our caller
		 * only incremented the RQ agent_barrier.
		 */
		(void) agent_barrier_get(agent);
		rq->ghost.blocked_in_run = false;
	}

	/*
	 * Unblock the agent if it has a signal to handle.
	 */
	if (unlikely(signal_pending(agent)))
		rq->ghost.blocked_in_run = false;

	/*
	 * If the agent is not in a state where it is productively scheduling
	 * then try to get it there as soon as possible. This includes the
	 * case where the kernel has posted new messages for the agent.
	 */
	if (!rq->ghost.blocked_in_run)
		next = agent;

	return next;
}

static inline void ghost_prepare_switch(struct rq *rq, struct task_struct *prev,
					struct task_struct *next)
{

	if (next) {
		next->ghost.last_runnable_at = 0;

		WARN_ON_ONCE(!on_ghost_rq(rq, next));
		if (likely(next != prev)) {
			struct ghost_status_word *sw;

			next->se.exec_start = rq_clock_task(rq);
			sw = next->ghost.status_word;
			WARN_ON_ONCE(sw->flags & GHOST_SW_TASK_ONCPU);
			ghost_sw_set_time(sw, ktime_get_ns());
			ghost_sw_set_flag(sw, GHOST_SW_TASK_ONCPU);
		} else {
			WARN_ON_ONCE(rq->ghost.must_resched &&
				     next != rq->ghost.agent);
		}
	}
}

/*
 * Produce voluntary task state change msgs first (e.g. TASK_BLOCKED,
 * TASK_YIELD in case they end up waking the local agent).
 *
 * Returns 'false' if 'prev' should not be considered for a preemption edge.
 *
 * The basic idea is to elide TASK_PREEMPTED if a voluntary task state change
 * msg was already produced for 'prev' (for e.g. agents don't expect to see a
 * TASK_PREEMPTED immediately after a TASK_BLOCKED).
 */
static bool ghost_produce_prev_msgs(struct rq *rq, struct task_struct *prev)
{
	if (!task_has_ghost_policy(prev))
		return false;

	/* Who watches the watchmen? */
	if (prev == rq->ghost.agent)
		return false;

	if (prev->ghost.new_task) {
		prev->ghost.new_task = false;
		ghost_task_new(rq, prev);
		ghost_wake_agent_of(prev);

		/*
		 * An oncpu task can switch into ghost and yield or block
		 * before getting offcpu. We don't want this leaking into
		 * the next time this task gets oncpu (for e.g. imagine
		 * 'yield_task' leaking and the task blocks the next time
		 * it gets oncpu).
		 */
		prev->ghost.blocked_task = false;
		prev->ghost.yield_task = false;
		return false;
	}

	/*
	 * 'prev' was running when it yielded but now that it's
	 * off the cpu we can safely let the agent know about it.
	 */
	if (prev->ghost.yield_task) {
		WARN_ON_ONCE(prev->ghost.blocked_task);
		prev->ghost.yield_task = false;
		ghost_task_yield(rq, prev);
		ghost_wake_agent_of(prev);
		return false;
	}

	if (prev->ghost.blocked_task) {
		prev->ghost.blocked_task = false;
		ghost_task_blocked(rq, prev);
		ghost_wake_agent_of(prev);
		return false;
	}

	return true;
}

static void ghost_latched_task_preempted(struct rq *rq)
{
	struct task_struct *latched = rq->ghost.latched_task;

	WARN_ON_ONCE(!rq->ghost.agent);

	if (task_has_ghost_policy(latched)) {
		/*
		 * Normally, TASK_LATCHED is not sent until we context switch to
		 * the task.  The agent is expecting this message before
		 * TASK_PREEMPT.
		 */
		if (rq->ghost.run_flags & SEND_TASK_LATCHED) {
			task_deliver_msg_latched(rq, latched, true);
			rq->ghost.run_flags &= ~SEND_TASK_LATCHED;
		}
		_ghost_task_preempted(rq, latched, true);
		ghost_wake_agent_of(latched);
	} else {
		/*
		 * Idle task was latched and agent must have made
		 * other arrangements to be notified that CPU is
		 * no longer idle (for e.g. NEED_CPU_NOT_IDLE).
		 */
		WARN_ON_ONCE(latched != rq->idle);
	}
	rq->ghost.latched_task = NULL;
}

static inline void ghost_update_boost_prio(struct task_struct *p,
					   bool preempted)
{
	if (preempted)
		ghost_sw_set_flag(p->ghost.status_word, GHOST_SW_BOOST_PRIO);
	else
		ghost_sw_clear_flag(p->ghost.status_word, GHOST_SW_BOOST_PRIO);
}

static struct task_struct *pick_next_ghost_agent(struct rq *rq)
{
	struct task_struct *agent = rq->ghost.agent;
	struct task_struct *next = NULL;
	int nr_running;
	bool preempted;
	struct task_struct *prev = rq->curr;

	if (!agent || !agent->on_rq)
		goto done;

	/*
	 * Evaluate after produce_prev_msgs() in case it wakes up the local
	 * agent.
	 */
	next = pick_agent(rq);

	/*
	 * 'preempted' is true if a higher priority sched_class (e.g. CFS)
	 * has runnable tasks. We use it as follows:
	 *
	 * 1. indicate via GHOST_SW_BOOST_PRIO that the agent must yield
	 *    the CPU asap.
	 *
	 * 2. produce a TASK_PREEMPTED msg on behalf of 'prev' (note that the
	 *    TASK_PREEMPTED msg could trigger a local agent wakeup; producing
	 *    the msg here as opposed to after pick_next_task() allows us to
	 *    eliminate one redundant context switch from 'ghost->CFS->agent'
	 *    to 'ghost->agent'.
	 */
	nr_running = rq->nr_running;
	WARN_ON_ONCE(nr_running < rq->ghost.ghost_nr_running);
	preempted = (nr_running > rq->ghost.ghost_nr_running);

	/* Preempted by local agent or another sched_class. */
	if (next || preempted) {
		/*
		 * Even though 'preempted' may be set, the task may have blocked
		 * or yielded.  check_prev_preemption tells us if this is an
		 * actual preemption: the task did not stop voluntarily.
		 */
		if (rq->ghost.check_prev_preemption) {
			/*
			 * Paranoia: force_offcpu guarantees that 'prev' does
			 * not stay oncpu after producing TASK_PREEMPTED(prev).
			 */
			ghost_task_preempted(rq, prev);
			ghost_wake_agent_of(prev);
			force_offcpu(rq, false);
			rq->ghost.check_prev_preemption = false;
		}

		/*
		 * CPU is switching to a non-ghost task while a task is latched.
		 *
		 * Treat this like latched_task preemption because we don't know
		 * when the CPU will be available again so no point in keeping
		 * it latched.
		 *
		 * If the DEFER_LATCHED_PREEMPTION_BY_AGENT run flag is set, we
		 * will defer preemption by the agent to the next tick. This
		 * helps to avoid spurious preemption due to the agent being
		 * runnable, while still bounding the time a latched task could
		 * face a scheduling blackout.
		 */
		if (rq->ghost.latched_task && (preempted ||
		    !(rq->ghost.run_flags & DEFER_LATCHED_PREEMPTION_BY_AGENT))) {
			ghost_latched_task_preempted(rq);
		}

		/* did the preemption msg wake up the local agent? */
		if (!next)
			next = pick_agent(rq);
	 }

	if (!next)
		goto done;

	ghost_update_boost_prio(next, preempted);
	ghost_prepare_switch(rq, prev, next);

done:
	return next;
}

static struct task_struct *_pick_next_task_ghost(struct rq *rq)
{
	struct task_struct *agent = rq->ghost.agent;
	struct task_struct *prev = rq->curr;
	struct task_struct *next = NULL;

	/*
	 * We made it to ghost's pick_next_task so no need to check whether
	 * 'prev' was preempted by a higher priority sched_class.
	 *
	 * We prefer to use an explicit signal over checking the sched_class
	 * of 'next' in ghost_prepare_task_switch() because sometimes even
	 * higher priority sched classes can pick 'rq->idle' to run next.
	 * (e.g. pick_next_task_fair() does this with core tagging enabled).
	 */
	if (rq->ghost.switchto_count == 0) {
		/*
		 * This is the only time we clear check_prev_preemption without
		 * sending a TASK_PREEMPT.
		 */
		if (rq->ghost.run_flags & ELIDE_PREEMPT)
			rq->ghost.check_prev_preemption = false;
	} else {
		WARN_ON_ONCE(rq->ghost.switchto_count > 0);

		/*
		 * We mark that the switchto chain has ended at the top of PNT
		 * (switchto_count < 0). Usually we will pick a different task
		 * (another sched_class or rq->ghost.latched_task) but this is
		 * not guaranteed (rq->lock can be dropped in PNT and runnable
		 * tasks can migrate to other cpus).
		 *
		 * We set 'must_resched' to guarantee a context switch on this
		 * CPU so the 'switchto_count' bookkeeping can be squared away
		 * via context_switch()->ghost_prepare_task_switch().
		 *
		 * Note that if 'prev' is forced offcpu we will still produce
		 * a TASK_PREEMPTED(prev) courtesy of 'check_prev_preemption'.
		 */
		rq->ghost.must_resched = true;

		/*
		 * Don't reset 'check_prev_preemption' here:
		 *
		 * This trip through pick_next_task() could be due to an agent
		 * initiated preemption while this cpu was in a switchto chain.
		 * We must produce a TASK_PREEMPTED for the oncpu task since
		 * the agent couldn't possibly know which task was preempted.
		 */
	}

	/*
	 * 'prev' may have entered ghost on a CPU which doesn't have an agent
	 * or the agent is not runnable. In either case, we need to get 'prev'
	 * off this CPU and let an agent (remote or local) decide where and
	 * when to bring it back.
	 */
	if (!agent || !agent->on_rq)
		return NULL;

	if (rq->ghost.latched_task) {
		uint32_t barrier;

		next = rq->ghost.latched_task;
		rq->ghost.latched_task = NULL;

		WARN_ON_ONCE(rq->curr == next);
		VM_BUG_ON(task_rq(next) != rq);

		if (next == rq->idle) {
			/*
			 * N.B. even though 'next' is the idle task this CPU
			 * is not "idle" (presumably the sibling is running
			 * a vcpu as part of a sync-group commit). Therefore
			 * we return 'rq->idle' directly as opposed to via
			 * pick_next_task_idle() and its side-effects.
			 */
			put_prev_task(rq, prev);
			return rq->idle;
		}

		/* Suppress barrier check in validate_next_task(). */
		barrier = task_barrier_get(next);
		if (validate_next_task(rq, next, barrier, NULL) ||
		    validate_next_offcpu(rq, next, NULL)) {
			/*
			 * Welp! A previously latched and validated
			 * task is now failing checks. Let the local
			 * agent figure out what to do.
			 */
			pr_warn("ghost: likely leaking task %d", next->pid);
			next = agent;
			rq->ghost.blocked_in_run = false;
		} else {
			if (unlikely(rq->ghost.run_flags & NEED_L1D_FLUSH))
				kvm_register_core_conflict(cpu_of(rq));
		}
		goto done;
	}

	/*
	 * Handle a couple of unusual code paths:
	 * - 'prev' blocked but it was woken up before it got off the
	 *   runqueue (see 'light' wakeup in ttwu_remote()).
	 * - 'prev' blocked voluntarily but __schedule() made it runnable
	 *   to handle a pending signal.
	 * - cond_resched() called __schedule(preempt) but there isn't
	 *   any higher priority task to switch to.
	 */
	if (task_has_ghost_policy(prev) && prev->state == TASK_RUNNING) {
		/*
		 * When an agent blocks via ghost_run() we end up here with
		 * 'prev == agent' via schedule(). Without the check below
		 * we will simply return 'prev' (aka the agent) from this
		 * function and subvert the blocking in ghost_run().
		 */
		if (unlikely(prev != agent && !rq->ghost.must_resched)) {
			next = prev;
			rq->ghost.check_prev_preemption = false;
			goto done;
		}
	}

done:
	if (unlikely(!next && rq->ghost.run_flags & RTLA_ON_IDLE)) {
		rq->ghost.blocked_in_run = false;
		return pick_next_ghost_agent(rq);
	}

	ghost_prepare_switch(rq, prev, next);
	rq->ghost.must_resched = false;

	return next;
}

static void _check_preempt_curr_ghost(struct rq *rq, struct task_struct *p,
				      int wake_flags)
{
	if (is_agent(rq, p)) {
		/*
		 * Agents always preempt.
		 *
		 * Agents can run in the high priority ghost agent class, but
		 * they belong to the lower priority ghost class. For this
		 * reason, we have special preemption handling for ghost agents
		 * directly in check_preeempt_curr(). Thus, we will rarely
		 * hit this case in check_preempt_curr_ghost(), since
		 * - agents don't move across cpus
		 * - a ghost thread running on the cpu implies that the agent
		 *   could not have been blocked
		 * One example where we _could_ hit this case is when we
		 * setsched a task into ghost on a cpu where the agent is
		 * blocked (and then wakes up before the task gets off cpu).
		 */
		resched_curr(rq);
	} else {
		/*
		 * The agent makes the preemption decision (if needed)
		 * when it notices that 'p' is runnable.
		 *
		 * The kernel can do nothing here because it does not
		 * implement scheduling policy.
		 */
	}
}

static void _yield_task_ghost(struct rq *rq)
{
	struct task_struct *curr = rq->curr;

	if (unlikely(is_agent(rq, curr))) {
		/* Agent should never yield in its critical section */
		WARN_ON_ONCE(rq->ghost.blocked_in_run);
		return;
	}

	/*
	 * Task is yielding so get it offcpu. We don't need the full
	 * resched_curr() functionality here because sched_yield()
	 * calls schedule() immediately after.
	 */
	if (rq->ghost.run_flags & RTLA_ON_YIELD)
		schedule_agent(rq, false);
	else
		force_offcpu(rq, false);

	/*
	 * Hold off on announcing that the task has yielded just yet.
	 *
	 * The agent is allowed to do a ghost_run() as soon as it sees
	 * the YIELD msg, but this task is oncpu without 'need_resched'
	 * so validate_next_task() will flag this as an error.
	 *
	 * Fix this by deferring the YIELD msg until the task is truly
	 * off the cpu.
	 *
	 * N.B. although 'rq->lock' is held here sched_yield() drops
	 * it before calling schedule() making the race with ghost_run()
	 * possible.
	 */
	WARN_ON_ONCE(curr->ghost.yield_task);
	curr->ghost.yield_task = true;
}

static void _set_cpus_allowed_ghost(struct task_struct *p,
				    const struct cpumask *newmask, u32 flags)
{
	struct rq_flags rf;
	struct rq *rq = task_rq(p);
	bool locked = false;

	/*
	 * Agents: not allowed (rejected in __set_cpus_allowed_ptr);
	 * Normal ghost tasks: Notify the agents.
	 */
	WARN_ON_ONCE(is_agent(rq, p));

	/*
	 * do_set_cpus_allowed() mentions a case where we could arrive here
	 * without the rq->lock held, but message delivery requires rq->lock
	 * held.
	 */
	if (!raw_spin_is_locked(&rq->lock)) {
		__task_rq_lock(p, &rf);
		locked = true;
	}

	/*
	 * N.B. sched_setaffinity() can race with exit() such that the task
	 * is already dead and contents of 'p->ghost' are no longer valid.
	 *
	 * Task msg delivery handles this properly but be careful when
	 * accessing 'p->ghost' directly in this function.
	 */
	task_deliver_msg_affinity_changed(rq, p);

	if (locked)
		__task_rq_unlock(rq, &rf);

	set_cpus_allowed_common(p, newmask, flags);
}

static void _task_woken_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_status_word *sw = p->ghost.status_word;

	WARN_ON_ONCE(!task_on_rq_queued(p));

	/*
	 * If this is a "light" wakeup via ttwu_remote() then don't produce
	 * a TASK_WAKEUP msg because we haven't actually dequeued the task.
	 */
	if (sw->flags & GHOST_SW_TASK_RUNNABLE)
		return;

	ghost_sw_set_flag(sw, GHOST_SW_TASK_RUNNABLE);

	if (unlikely(p->ghost.new_task)) {
		p->ghost.new_task = false;
		ghost_task_new(rq, p);
		goto done;
	}
	task_deliver_msg_wakeup(rq, p);
done:
	ghost_wake_agent_of(p);
}

/*
 * Migrate 'next' (if necessary) in preparation to run it on 'cpu'.
 *
 * An important side-effect is that 'next' is guaranteed to not be
 * cached on any cpu when this function returns (e.g. latched_task).
 */
static struct rq *ghost_move_task(struct rq *rq, struct task_struct *next,
				  int cpu, struct rq_flags *rf)
{
	lockdep_assert_held(&rq->lock);
	lockdep_assert_held(&next->pi_lock);

	WARN_ON_ONCE(rq->ghost.skip_latched_preemption);

	/*
	 * Cleared in invalidate_cached_tasks() via move_queued_task()
	 * and _dequeue_task_ghost(). We cannot clear it here because
	 * move_queued_task() will release rq->lock (the rq returned
	 * by move_queued_task() is different than the one passed in).
	 */
	rq->ghost.skip_latched_preemption = true;

	/*
	 * 'next' was enqueued on a different CPU than where the agent
	 * wants to run it now so migrate it to this runqueue before
	 * switching to it.
	 */
	if (unlikely(task_cpu(next) != cpu)) {
		VM_BUG_ON(task_running(rq, next));
		VM_BUG_ON(!task_on_rq_queued(next));
		update_rq_clock(rq);
		rq = move_queued_task(rq, rf, next, cpu);
	} else {
		invalidate_cached_tasks(rq, next);
	}

	return rq;
}

static int _ghost_mmap_common(struct vm_area_struct *vma, ulong mapsize)
{
	static const struct vm_operations_struct ghost_vm_ops = {};

	/*
	 * VM_MAYSHARE indicates that MAP_SHARED was set in 'mmap' flags.
	 *
	 * Checking VM_SHARED seems intuitive here but this bit is cleared
	 * by do_mmap() if the underlying file is readonly (as is the case
	 * for a sw_region file).
	 */
	if (!(vma->vm_flags & VM_MAYSHARE))
		return -EINVAL;

	/*
	 * Mappings are always readable and 'do_mmap()' ensures that
	 * FMODE_WRITE and VM_WRITE are coherent so the only remaining
	 * check is against VM_EXEC.
	 */
	if (vma->vm_flags & VM_EXEC)
		return -EACCES;

	/* The entire region must be mapped */
	if (vma->vm_pgoff)
		return -EINVAL;

	if (vma->vm_end - vma->vm_start != mapsize)
		return -EINVAL;

	/*
	 * Don't allow mprotect(2) to relax permissions beyond what
	 * would have been allowed by this function.
	 *
	 * Mappings always readable and 'do_mmap()' ensures that
	 * FMODE_WRITE and VM_MAYWRITE are coherent so just clear
	 * VM_MAYEXEC here.
	 */
	vma->vm_flags &= ~VM_MAYEXEC;
	vma->vm_flags |= VM_DONTCOPY;

	/*
	 * Initialize 'vma->vm_ops' to avoid vma_is_anonymous() false-positive.
	 */
	vma->vm_ops = &ghost_vm_ops;
	return 0;
}

/*
 * Helper function for mapping status_word and similar regions into userspace.
 *
 * 'addr' must have been obtained from vmalloc_user().
 */
static int ghost_region_mmap(struct file *file, struct vm_area_struct *vma,
			     void *addr, ulong mapsize)
{
	int error;

	error = _ghost_mmap_common(vma, mapsize);
	if (!error)
		error = remap_vmalloc_range(vma, addr, 0);

	return error;
}

static int ghost_cpu_data_mmap(struct file *file, struct vm_area_struct *vma,
			       struct ghost_cpu_data **cpu_data, ulong mapsize)
{
	int error;
	unsigned long uaddr;

	BUILD_BUG_ON(sizeof(struct ghost_cpu_data) != PAGE_SIZE);

	error = _ghost_mmap_common(vma, mapsize);
	if (error)
		return error;

	for (uaddr = vma->vm_start; uaddr < vma->vm_end; uaddr += PAGE_SIZE) {
		error = remap_vmalloc_range_partial(vma, uaddr, *cpu_data++,
							0, PAGE_SIZE);
		if (WARN_ON_ONCE(error)) {
			/*
			 * do_mmap() will cleanup the partially populated VMA.
			 */
			break;
		}
	}
	return error;
}

struct queue_notifier {
	struct ghost_agent_wakeup winfo[GHOST_MAX_WINFO];
	struct rcu_head rcu;
	unsigned int wnum;	/* number of valid entries in winfo[] */
};

struct ghost_queue {
	/*
	 * 'lock' protects 'refs' as well as the association between a
	 *  message source and its queue and status_word.
	 *
	 *  See go/ghost-queue-change for more details.
	 */
	spinlock_t lock;
	struct kref kref;

	struct ghost_enclave *enclave;

	/* 'ring' and 'nelems' are read-only after initialization */
	struct ghost_ring *ring;
	uint32_t nelems;	/* power-of-2 size of ghost_ring.msgs[] */

	void *addr;		/*
				 * address of vmalloc'ed region; this is
				 * deliberately a 'void *' instead of
				 * 'ghost_queue_header *' so we don't
				 * read it even inadvertently.
				 */

	ulong mapsize;		/* size of the vmalloc'ed region */

	struct queue_notifier *notifier;  /* rcu-protected agent wakeup info */

	struct rcu_head rcu;		/* deferred free glue */
	struct work_struct free_work;
};

/*
 * Free the memory resources associated with the ghost_queue (must be called
 * in sleepable process context).
 */
static void __queue_free_work(struct work_struct *work)
{
	struct ghost_queue *q = container_of(work, struct ghost_queue,
					     free_work);
	vfree(q->addr);
	kfree(q->notifier);
	kfree(q);
}

static void _queue_free_rcu_callback(struct rcu_head *rhp)
{
	struct ghost_queue *q = container_of(rhp, struct ghost_queue, rcu);

	/*
	 * Further defer work to a preemptible process context: the rcu
	 * callback may be called from a softirq context and cannot block.
	 */
	schedule_work(&q->free_work);
}

static void __queue_kref_release(struct kref *k)
{
	struct ghost_queue *q = container_of(k, struct ghost_queue, kref);

	/*
	 * We may be called from awkward contexts that hold scheduler
	 * locks or that are non-preemptible and this runs afoul of
	 * sleepable locks taken during vfree(q->addr).
	 *
	 * Defer freeing of queue memory to an rcu callback (this has
	 * nothing to do with rcu and we use it solely for convenience).
	 */
	call_rcu(&q->rcu, _queue_free_rcu_callback);
}

static inline void queue_decref(struct ghost_queue *q)
{
	kref_put(&q->kref, __queue_kref_release);
}

static inline void queue_incref(struct ghost_queue *q)
{
	kref_get(&q->kref);
}

/*
 * Callback from ghost_add_cpus().  Caller must hold e->lock.
 */
static void ___enclave_add_cpu(struct ghost_enclave *e, int cpu)
{
	struct ghost_txn *txn;

	VM_BUG_ON(!spin_is_locked(&e->lock));
	VM_BUG_ON(cpumask_test_cpu(cpu, &e->cpus));

	txn = &e->cpu_data[cpu]->txn;
	/*
	 * Reinitialize in case this txn was used by this enclave before, such
	 * as if a cpu was removed and readded.
	 */
	memset(txn, 0, sizeof(*txn));

	txn->cpu = cpu;
	txn->version = GHOST_TXN_VERSION;
	txn->u.sync_group_owner = -1;
	txn->state = GHOST_TXN_COMPLETE;

	cpumask_set_cpu(cpu, &e->cpus);
	rcu_assign_pointer(per_cpu(ghost_txn, cpu), txn);
}

/* Caller must hold e->lock and synchronize_rcu() on return */
static void __enclave_remove_cpu(struct ghost_enclave *e, int cpu)
{
	VM_BUG_ON(!spin_is_locked(&e->lock));
	VM_BUG_ON(!cpumask_test_cpu(cpu, &e->cpus));

	rcu_assign_pointer(per_cpu(ghost_txn, cpu), NULL);
	cpumask_clear_cpu(cpu, &e->cpus);
	ghost_remove_cpu(e, cpu);
}

/*
 * Undo anything done in ghost_create_enclave().  We also free the SW regions
 * here, even though they were created at runtime.  Once a swr is created, it
 * persists until enclave_release.  This keeps refcounting simpler.
 */
static void enclave_actual_release(struct work_struct *w)
{
	struct ghost_enclave *e = container_of(w, struct ghost_enclave,
					       enclave_actual_release);
	struct ghost_sw_region *swr, *temp;
	int cpu;

	list_for_each_entry_safe(swr, temp, &e->sw_region_list, list)
		__sw_region_free(swr);

	/*
	 * Any inhibited tasks should have been "released" as a side-effect
	 * of freeing the status_word regions above.
	 */
	WARN_ON_ONCE(!list_empty(&e->inhibited_task_list));

	for_each_possible_cpu(cpu)
		vfree(e->cpu_data[cpu]);

	kfree(e->cpu_data);
	kfree(e);
}

static void enclave_release(struct kref *k)
{
	struct ghost_enclave *e = container_of(k, struct ghost_enclave, kref);

	VM_BUG_ON(!cpumask_empty(&e->cpus));

	/*
	 * enclave_release may be called from a non-sleepable context.  However,
	 * freeing the enclave could block/sleep. vfree -> __vunmap ->
	 * remove_vm_area.  Solve this by kicking a worker to do the actual
	 * cleanup.
	 */
	if (!schedule_work(&e->enclave_actual_release))
		WARN_ONCE(1, "enclave released twice?!?");
}

static void enclave_reap_tasks(struct work_struct *work)
{
	struct ghost_enclave *e = container_of(work, struct ghost_enclave,
					       task_reaper);
	unsigned long irq_fl;
	struct task_struct *t, *prev = NULL;
	int ret = 0;
	static const struct sched_param param = { .sched_priority = 0 };

	spin_lock_irqsave(&e->lock, irq_fl);
	WARN_ON_ONCE(!enclave_is_reapable(e));

	/*
	 * The moment we unlock, the task could exit.  We can't lock the task
	 * either, since the lock ordering is pi_lock->e_lock.  Once we let go
	 * of e->lock, we can't walk the list either.  Assuming setscheduler
	 * succeeds, the task should be gone next time we look.  That might not
	 * be true for TASK_DEAD, so we can skip those.
	 *
	 * The only error condition here is if we see the same non-dead task on
	 * the list after calling setscheduler.  We'll abort and possibly leak
	 * resources, but at least we won't lock up the system.  We exit the
	 * 'next_item' loop when:
	 * - the list is empty,
	 * - the list only contains TASK_DEAD, or
	 * - we abort
	 */
next_item:
	list_for_each_entry(t, &e->task_list, ghost.task_list) {
		if (t->state == TASK_DEAD)
			continue;
		if (t == prev) {
			WARN(1, "Reaper saw %d again, aborting!", t->pid);
			break;
		}
		prev = t;

		get_task_struct(t);
		spin_unlock_irqrestore(&e->lock, irq_fl);

		ret = sched_setscheduler_nocheck(t, SCHED_NORMAL, &param);

		put_task_struct(t);
		spin_lock_irqsave(&e->lock, irq_fl);

		WARN_ONCE(ret && ret != -ESRCH,
			  "Failed to setsched pid %d, ret %d, state 0x%lx)!",
			  t->pid, ret, t->state);

		goto next_item;
	}

	spin_unlock_irqrestore(&e->lock, irq_fl);

	kref_put(&e->kref, enclave_release);
}

/*
 * Here we can trigger any destruction we want, such as killing agents, kicking
 * tasks to CFS, etc.  Undo things that were done at runtime.
 *
 * The enclave itself isn't freed until enclave_release().
 */
static void __ghost_destroy_enclave(struct ghost_enclave *e)
{
	ulong flags;
	int cpu;

	spin_lock_irqsave(&e->lock, flags);
	if (enclave_is_dying(e)) {
		spin_unlock_irqrestore(&e->lock, flags);
		return;
	}
	/* Don't accept new agents into the enclave or changes to its cpuset */
	e->is_dying = ENCLAVE_IS_DYING;

	/*
	 * At this point, no one can change the cpus or add new agents, since
	 * e->is_dying.
	 *
	 * Our goal here is to get the agents (if any) off the cpus.  We could
	 * try kicking them to CFS, and yanking them out of rq->ghost.agent, but
	 * that is a little tricky.  Are they blocked_in_run?  Are they running
	 * ghost code that assumes they are the agent?
	 *
	 * Another approach is to kill them, then wait for them to finish.  When
	 * they are done, we can return the cpu to the system.  The trick is
	 * that we can't wait while holding locks: they could be blocked on I/O.
	 * They could also be *this* cpu.
	 *
	 * To handle this, we defer the cpu removal until the agent exits from
	 * ghost.  Since our enclave is dying, we can unlock and not worry about
	 * any agent joining the enclave or the cpus changing.  Since we don't
	 * give the cpu back to the system right away, we don't have to worry
	 * about anyone reusing the rq's agent fields.
	 *
	 * Note that pcpu->enclave is still set until the agent task exits a
	 * given cpu.  We must follow the pattern of:
	 *   1) pcpu->enclave = NULL
	 *   2) synchronize_rcu()
	 *   3) decref the enclave
	 * because pcpu->enclave is protected and kreffable during
	 * rcu_read_lock().
	 *
	 * All three steps are handled in release_from_ghost().  We tell the
	 * agent to do this via agent->ghost.__agent_decref_enclave.  This needs
	 * to be per-agent, and not per-rq, since the moment we return the cpu
	 * to the system, another enclave and agent can reuse the fields in
	 * rq->ghost.
	 *
	 * Note the agent could be leaving ghost of its own volition
	 * concurrently; the enclave lock ensures that if we see an agent, it
	 * will remove the cpu when it exits.  And if not, we fully remove it
	 * here.  We make that decision before we unlock in the loop below.
	 *
	 * Why do we unlock?  Because send_sig grabs the pi_lock, and the lock
	 * ordering is pi -> rq -> e.  This is safe, since the lock is no longer
	 * protecting invariants.  The trick is that we rely on is_dying to
	 * prevent any of the changes to the enclave that we were concerned with
	 * (agent arrival or cpu changes).  And once we decide that an agent
	 * should call __enclave_return_cpu(), that decision is set in stone.
	 */

	for_each_cpu(cpu, &e->cpus) {
		struct rq *rq = cpu_rq(cpu);
		struct task_struct *agent;

		if (!rq->ghost.agent) {
			__enclave_remove_cpu(e, cpu);
			continue;
		}
		agent = rq->ghost.agent;
		kref_get(&e->kref);
		agent->ghost.__agent_decref_enclave = e;
		/*
		 * We can't force_sig().  The task might be exiting and losing
		 * its sighand_struct.  send_sig_info() checks for that.  We
		 * also can't hold the enclave lock.
		 *
		 * As soon as we unlock, the agent could exit on its own too.
		 * We still need to poke it to make sure it dies, and since it
		 * might be dying on its own, we need to get a refcount while we
		 * poke it.
		 */
		get_task_struct(agent);
		spin_unlock_irqrestore(&e->lock, flags);
		send_sig_info(SIGKILL, SEND_SIG_PRIV, agent);
		put_task_struct(agent);
		spin_lock_irqsave(&e->lock, flags);
	}
	spin_unlock_irqrestore(&e->lock, flags);

	synchronize_rcu();	/* Required after removing a cpu */

	/*
	 * It is safe to reap all tasks in the enclave only _after_
	 * synchronize_rcu returns: we have unpublished the enclave cpus
	 * and synchronize_rcu() guarantees that any older rcu read-side
	 * critical sections in find_task_by_gtid() have completed.
	 *
	 * Since 'e->lock' is dropped before synchronize_rcu we must
	 * prevent enclave_add_task() from sneaking in and scheduling
	 * the task reaper before synchronize_rcu returns.
	 *
	 * This is indicated by or'ing ENCLAVE_IS_REAPABLE into 'e->is_dying'.
	 */
	spin_lock_irqsave(&e->lock, flags);
	e->is_dying |= ENCLAVE_IS_REAPABLE;
	spin_unlock_irqrestore(&e->lock, flags);

	kref_get(&e->kref);	/* Reaper gets a kref */
	if (!schedule_work(&e->task_reaper))
		kref_put(&e->kref, enclave_release);

	/*
	 * Removes the enclave and all of its files from ghostfs.  There may
	 * still be open FDs, each of which holds a reference.  When the last FD
	 * is closed, we'll release and free.
	 */
	kernfs_remove(e->enclave_dir);

	kref_put(&e->kref, enclave_release);
}

static void enclave_destroyer(struct work_struct *work)
{
	struct ghost_enclave *e = container_of(work, struct ghost_enclave,
					       enclave_destroyer);

	__ghost_destroy_enclave(e);
	kref_put(&e->kref, enclave_release);
}

static void ghost_destroy_enclave(struct ghost_enclave *e)
{
	/*
	 * Defer destruction to a CFS task.  Need this in case we're in IRQ ctx
	 * or if current is in the enclave.
	 */
	kref_get(&e->kref);
	if (!schedule_work(&e->enclave_destroyer))
		kref_put(&e->kref, enclave_release);
}

/*
 * Sets the cpus of the enclave to `cpus`, adding and removing as necessary.
 * Returns an error code on failure and does not change the enclave.  Will fail
 * if a cpu is in another enclave.
 */
static int ghost_enclave_set_cpus(struct ghost_enclave *e,
				  const struct cpumask *cpus)
{
	unsigned long flags;
	unsigned int cpu;
	int ret = 0;
	cpumask_var_t add, del;

	if (!alloc_cpumask_var(&add, GFP_KERNEL))
		return -ENOMEM;
	if (!alloc_cpumask_var(&del, GFP_KERNEL)) {
		free_cpumask_var(add);
		return -ENOMEM;
	}

	spin_lock_irqsave(&e->lock, flags);

	if (enclave_is_dying(e)) {
		ret = -EXDEV;
		goto out_e;
	}

	cpumask_andnot(add, cpus, &e->cpus);
	cpumask_andnot(del, &e->cpus, cpus);

	for_each_cpu(cpu, del) {
		/*
		 * No need for an rq lock to read ghost.agent.  Both the enclave
		 * and the rq locks are required to *write* rq->ghost.agent.
		 */
		if (cpu_rq(cpu)->ghost.agent) {
			ret = -EEXIST;
			goto out_e;
		}
	}

	for_each_cpu(cpu, add) {
		if (!cpu_online(cpu)) {
			ret = -ENODEV;
			goto out_e;
		}
	}

	ret = ghost_add_cpus(e, add);
	if (ret)
		goto out_e;

	for_each_cpu(cpu, del)
		__enclave_remove_cpu(e, cpu);

out_e:
	spin_unlock_irqrestore(&e->lock, flags);

	synchronize_rcu();	/* Required after removing a cpu */

	free_cpumask_var(add);
	free_cpumask_var(del);

	return ret;
}

static struct ghost_queue *fd_to_queue(struct fd f)
{
	if (!f.file)
		return NULL;
	if (f.file->f_op != &queue_fops)
		return NULL;
	return f.file->private_data;
}

static void enclave_add_task(struct ghost_enclave *e, struct task_struct *p)
{
	ulong flags;

	if (p->ghost.agent)
		return;
	spin_lock_irqsave(&e->lock, flags);
	if (enclave_is_reapable(e)) {
		/*
		 * The task entered as the enclave was dying, and likely will
		 * miss the reaper.
		 */
		submit_enclave_work(e, task_rq(p), /*run_task_reaper=*/true, 0);
	}
	WARN_ON_ONCE(!list_empty(&p->ghost.task_list));
	list_add_tail(&p->ghost.task_list, &e->task_list);
	e->nr_tasks++;
	spin_unlock_irqrestore(&e->lock, flags);
}

/* Hold the enclave lock */
static void __enclave_remove_task(struct ghost_enclave *e,
				  struct task_struct *p)
{
	lockdep_assert_held(&e->lock);

	if (p->ghost.agent)
		return;
	WARN_ON_ONCE(list_empty(&p->ghost.task_list));
	list_del_init(&p->ghost.task_list);
	e->nr_tasks--;
}

/*
 * Run f() on every task in the enclave.  There's no guarantee p is still in the
 * enclave, so f() may have to check for it.
 */
static int enclave_for_each_task(struct ghost_enclave *e,
				 void (*f)(struct ghost_enclave *e,
					   struct task_struct *p, void *arg),
				 void *arg)
{
	unsigned long irq_fl;
	struct task_struct **for_each;
	size_t nr_tasks = 0;
	struct task_struct *p;
	int i;

	spin_lock_irqsave(&e->lock, irq_fl);

	/* Don't hold e->lock during f(), since f() may grab the rq lock. */
	for_each = kcalloc(e->nr_tasks, sizeof(struct task_struct *),
			   GFP_ATOMIC);
	if (WARN_ON_ONCE(!for_each)) {
		spin_unlock_irqrestore(&e->lock, irq_fl);
		return -ENOMEM;
	}
	list_for_each_entry(p, &e->task_list, ghost.task_list) {
		if (WARN_ON_ONCE(nr_tasks >= e->nr_tasks))
			break;
		get_task_struct(p);
		for_each[nr_tasks++] = p;
	}
	spin_unlock_irqrestore(&e->lock, irq_fl);

	for (i = 0; i < nr_tasks; i++) {
		p = for_each[i];
		f(e, p, arg);
		put_task_struct(p);
	}
	kfree(for_each);

	return 0;
}

static void enclave_add_sw_region(struct ghost_enclave *e,
				  struct ghost_sw_region *region)
{
	ulong flags;

	spin_lock_irqsave(&e->lock, flags);
	list_add_tail(&region->list, &e->sw_region_list);
	spin_unlock_irqrestore(&e->lock, flags);
}

static inline struct ghost_status_word *
first_status_word(struct ghost_sw_region_header *h)
{
	return (struct ghost_status_word *)((char *)h + h->start);
}

static inline bool status_word_inuse(struct ghost_status_word *sw)
{
	return sw->flags & GHOST_SW_F_INUSE;
}

static inline bool status_word_canfree(struct ghost_status_word *sw)
{
	return sw->flags & GHOST_SW_F_CANFREE;
}

static inline bool status_word_allocated(struct ghost_status_word *sw)
{
	return sw->flags & GHOST_SW_F_ALLOCATED;
}

static int free_status_word_locked(struct ghost_enclave *e,
				   struct ghost_status_word *sw)
{
	int error = -ENOENT;
	struct ghost_sw_region *region;
	struct ghost_sw_region_header *header;
	struct ghost_status_word *first, *limit;

	VM_BUG_ON(!spin_is_locked(&e->lock));
	list_for_each_entry(region, &e->sw_region_list, list) {
		header = region->header;
		first = first_status_word(header);
		limit = &first[header->capacity];
		if (sw >= first && sw < limit) {
			if (!status_word_allocated(sw)) {
				/*
				 * Trying to free an already free status word?
				 */
				error = -EALREADY;
			} else {
				memset(sw, 0, sizeof(struct ghost_status_word));
				header->available++;
				error = 0;	/* success */
			}
			break;
		}
	}
	return error;
}

static struct ghost_status_word *lookup_status_word_locked(
		struct ghost_enclave *e, uint32_t id, uint32_t index)
{
	struct ghost_sw_region *region;
	struct ghost_sw_region_header *header;
	struct ghost_status_word *sw = NULL;

	VM_BUG_ON(!spin_is_locked(&e->lock));
	list_for_each_entry(region, &e->sw_region_list, list) {
		header = region->header;
		if (header->id == id) {
			if (index < header->capacity)
				sw = first_status_word(header) + index;
			break;
		}
	}
	return sw;
}

static struct ghost_status_word *
alloc_status_word_locked(struct ghost_enclave *e)
{
	struct ghost_sw_region *region;
	struct ghost_sw_region_header *header = NULL;
	struct ghost_status_word *sw, *found = NULL;
	uint32_t n;

	VM_BUG_ON(!spin_is_locked(&e->lock));

	/* Look for a sw_region that has at least one free status_word. */
	list_for_each_entry(region, &e->sw_region_list, list) {
		if (region->header->available) {
			header = region->header;    /* got one */
			break;
		}
	}

	/* No free slots available in any status_word region. */
	if (!header)
		goto done;

	sw = first_status_word(header);
	for (n = 0; n < header->capacity; n++) {
		found = &sw[region->alloc_scan_start++];
		/* Wrap around to the start if we are past the end. */
		if (region->alloc_scan_start >= header->capacity)
			region->alloc_scan_start = 0;

		/*
		 * If this slot is free then claim it and adjust 'available'.
		 */
		if (!status_word_allocated(found)) {
			found->flags = GHOST_SW_F_ALLOCATED;
			header->available--;
			break;
		}
	}
	VM_BUG_ON(n >= header->capacity);
done:
	return found;
}

static void ghost_initialize_status_word(struct task_struct *p)
{
	struct ghost_status_word *sw = p->ghost.status_word;

	if (WARN_ON_ONCE(!p->ghost.status_word))
		return;

	if (WARN_ON_ONCE(sw->flags != GHOST_SW_F_ALLOCATED))
		return;

	sw->gtid = gtid(p);
	sw->barrier = 0;
	sw->runtime = 0;

	/*
	 * Order is important to ensure that agent observes a fully formed
	 * status_word when discovering tasks from the status_word region.
	 */
	ghost_sw_set_flag(sw, GHOST_SW_F_INUSE);
}

/*
 * Prepare task 'p' to participate in ghost scheduling.
 *
 * Hold the enclave lock.
 *
 * The underlying 'task_struct' is stable because:
 * - it is protected by 'p->pi_lock' (called via sched_setscheduler).
 * - it is being created (called via sched_fork).
 */
static int __ghost_prep_task(struct ghost_enclave *e, struct task_struct *p,
			     struct ghost_queue *q, bool forked)
{
	struct ghost_status_word *sw;
	int error = 0;

	WARN_ON_ONCE(p->ghost.status_word);
	WARN_ON_ONCE(p->ghost.dst_q);
	WARN_ON_ONCE(p->ghost.enclave);

	lockdep_assert_held(&e->lock);

	/*
	 * Clean up state from a previous incarnation (e.g. ghost->cfs->ghost).
	 */
	sched_ghost_entity_init(p);

	/*
	 * This prevents us from joining a dying enclave and grabbing the
	 * enclave's kref.  However, it is possible for the enclave to die
	 * before we get enqueued (see uses of `new_task` and ghost_task_new()).
	 */
	if (enclave_is_dying(e)) {
		error = -EXDEV;
		goto done;
	}

	/*
	 * If msg inhibition is in effect then make sure that the task does
	 * not jump ABI versions (i.e. it must setsched into an enclave that
	 * has the same abi version as the one it belonged to earlier).
	 *
	 * Note that this is trivially true if the task switches back into
	 * the same enclave.
	 *
	 * Why? different enclaves may be at different ABI versions so when
	 * the status_word is freed from the original enclave we may not have
	 * access to the function that produces TASK_NEW in the new ABI.
	 */
	if (p->inhibit_task_msgs) {
		/*
		 * 'inhibit_task_msgs' is used as a boolean but it actually
		 * holds the abi of the enclave the task departed from.
		 */
		uint old_abi = p->inhibit_task_msgs;
		if (old_abi != enclave_abi(e)) {
			error = -EINVAL;
			goto done;
		}
	}

	if (q) {
		/*
		 * It's possible for a client task to have no queue: it may have
		 * arrived before an agent set the default queue during an agent
		 * update.
		 *
		 * However, agent tasks should have provided some queue: either
		 * explicitly or the default queue.  We handle this case in
		 * ghost_prep_agent().
		 */
		queue_incref(q);
	}
	p->ghost.dst_q = q;

	/* Allocate a status_word */
	sw = alloc_status_word_locked(e);
	if (sw == NULL) {
		error = -ENOMEM;
		goto done;
	}

	kref_get(&e->kref);
	p->ghost.enclave = e;
	p->ghost.status_word = sw;
	p->ghost.new_task = forked;

	if (!forked) {
		ghost_initialize_status_word(p);
	} else {
		/*
		 * Caller will initialize status_word after allocating gtid
		 * (see copy_process).
		 */
	}
done:
	if (error) {
		if (p->ghost.dst_q) {
			queue_decref(p->ghost.dst_q);
			p->ghost.dst_q = NULL;
		}

		if (p->ghost.status_word) {
			free_status_word_locked(e, p->ghost.status_word);
			p->ghost.status_word = NULL;
		}
	}
	return error;
}

/*
 * Caller must call ghost_uninhibit_task_msgs(p) on the task returned from
 * this function. Ideally we would have had a single function that removes
 * the task from the 'inhibited_task_list' and enables msgs for this task,
 * but we must split them up due to locking requirements (removing the
 * task requires enclave to be locked whereas ungating msgs requires
 * that no locks are held).
 */
static struct task_struct *
__enclave_remove_inhibited_task(struct ghost_enclave *e, gtid_t gtid)
{
	struct task_struct *p;

	if (kref_read(&e->kref)) {
		lockdep_assert_held(&e->lock);
	} else {
		/*
		 * No more references to the enclave (called from
		 * enclave_actual_release()).
		 */
	}

	/*
	 * N.B. cannot use find_task_by_gtid() to do the {gtid->task_struct}
	 * lookup here since that function expects to be called in an agent
	 * context.
	 */
	list_for_each_entry(p, &e->inhibited_task_list, inhibited_task_list) {
		if (p->gtid == gtid) {
			list_del_init(&p->inhibited_task_list);
			return p;
		}
	}
	return NULL;
}

static void ghost_uninhibit_task_msgs(struct task_struct *p)
{
	struct rq_flags rf;
	struct rq *rq;

	if (WARN_ON_ONCE(!p->inhibit_task_msgs))
		goto done;

	rq = task_rq_lock(p, &rf);
	if (p->state != TASK_DEAD) {
		/*
		 * 'inhibit_task_msgs' is used as a boolean but it actually
		 * holds the abi of the enclave the task departed from.
		 */
		const uint old_abi = p->inhibit_task_msgs;

		p->inhibit_task_msgs = 0;	/* open the gate */

		if (ghost_class(p->sched_class)) {
			WARN_ON_ONCE(old_abi != enclave_abi(p->ghost.enclave));
			if (p->ghost.new_task) {
				/*
				 * Task is oncpu and will produce TASK_NEW on
				 * the next scheduling edge.
				 */
				WARN_ON_ONCE(!task_running(rq, p));
			} else {
				const bool runnable = task_on_rq_queued(p);
				task_deliver_msg_task_new(rq, p, runnable);
				ghost_wake_agent_of(p);
			}
		} else {
			/*
			 * Nothing: we opened the gate above so if/when the
			 * task switches into ghost we'll produce a TASK_NEW
			 * msg immediately.
			 */
		}
	} else {
		/*
		 * There are three possibilities here:
		 *
		 * 1. task has finished scheduling for the last time and the
		 * task_dead() callback is happening concurrently or has
		 * finished executing.
		 *
		 * 2. task is in the middle of its last __schedule() and we
		 * sneaked in while rq->lock was dropped in one of the PNT
		 * sched_class callbacks.
		 *
		 * 3. task is about to __schedule() for the very last time
		 * (running concurrently in do_task_dead() or spinning on
		 * rq->lock in __schedule()).
		 *
		 * It would be problematic if we produced TASK_NEW in the
		 * first scenario since there is no guarantee that we'll
		 * also produce the corresponding TASK_DEAD and because we
		 * cannot distinguish (1) from (2) or (3) we won't produce
		 * the TASK_NEW msg or clear p->inhibit_task_msgs.
		 *
		 * Note that release_from_ghost() will free the status_word
		 * in all of these cases.
		 */
	}
	task_rq_unlock(rq, p, &rf);

done:
	put_task_struct(p);
}

/*
 * Only called from enclave_release.  Any users of this SWR had an enclave kref,
 * so if we're here, they must all have stopped using their SW.  This also
 * includes anyone mmapping the ghostfs file.
 *
 * This does not mean that the SW's were fully freed.  They may have been in the
 * GHOST_SW_F_CANFREE state.  Userspace may have failed to free them, due to a
 * crash.
 */
static int __sw_region_free(struct ghost_sw_region *swr)
{
	struct ghost_sw_region_header *header = swr->header;
	struct ghost_status_word *sw;
	struct task_struct *p;

	/*
	 * Enclave is destroyed so scan all status words to find tasks
	 * where msg gating is in effect (and then turn it off because
	 * any agent that could have been handling msgs from an earlier
	 * incarnation is dead).
	 */
	for (sw = first_status_word(header);
	     sw < first_status_word(header) + header->capacity; sw++) {
		/*
		 * inuse  canfree
		 *   0       0		empty slot
		 *   0       1		not expected (see WARN below)
		 *   1       0		not expected (see WARN below)
		 *   1       1		task died or departed (either due to
		 *			task_reaper or organically while the
		 *			enclave was being destroyed).
		 */
		if (!status_word_inuse(sw)) {
			WARN_ON_ONCE(status_word_canfree(sw));
			continue;
		}

		if (WARN_ON_ONCE(!status_word_canfree(sw)))
			continue;

		if (!(sw->flags & GHOST_SW_TASK_MSG_GATED)) {
			/*
			 * task died while enclave was being destroyed or a
			 * misbehaving agent did not free status word in its
			 * TASK_DEAD handler.
			 */
			continue;
		}

		p = __enclave_remove_inhibited_task(swr->enclave, sw->gtid);
		if (WARN_ON_ONCE(!p))
			continue;

		ghost_uninhibit_task_msgs(p);
	}

	list_del(&swr->list);

	vfree(header);
	kfree(swr);

	/* XXX memcg uncharge */

	return 0;
}

static size_t calculate_sw_region_size(void)
{
	/*
	 * Arbitrary number, but if we subtract off the swr header, we're
	 * likely to get close to the number we want when we PAGE_ALIGN.
	 */
	#define GHOST_NR_SW_ELEMS (65536 - \
		DIV_ROUND_UP(sizeof(struct ghost_sw_region_header), \
			     sizeof(struct ghost_status_word)))
	size_t size;

	size = sizeof(struct ghost_sw_region_header);
	size += GHOST_NR_SW_ELEMS * sizeof(struct ghost_status_word);
	size = PAGE_ALIGN(size);

	return size;
}

/*
 * Returns a pointer to the region.  Once created, a SW region will not be
 * removed until the enclave is freed.
 *
 * Returns an ERR_PTR on error.
 */
static struct ghost_sw_region *ghost_create_sw_region(struct ghost_enclave *e,
						      unsigned int id,
						      unsigned int node)
{
	struct ghost_sw_region *swr;
	struct ghost_sw_region_header *h;

	if (node < 0 || node >= nr_node_ids || !node_online(node))
		return ERR_PTR(-ENODEV);

	swr = kzalloc_node(sizeof(struct ghost_sw_region), GFP_KERNEL, node);
	if (!swr)
		return ERR_PTR(-ENOMEM);

	INIT_LIST_HEAD(&swr->list);
	swr->mmap_sz = calculate_sw_region_size();
	swr->header = vmalloc_user_node_flags(swr->mmap_sz, node, GFP_KERNEL);
	if (!swr->header) {
		kfree(swr);
		return ERR_PTR(-ENOMEM);
	}

	h = swr->header;
	h->id = id;
	h->numa_node = node;
	h->version = GHOST_SW_REGION_VERSION;
	h->start = sizeof(struct ghost_sw_region_header);
	h->capacity = (swr->mmap_sz - h->start) /
		sizeof(struct ghost_status_word);
	h->available = h->capacity;

	enclave_add_sw_region(e, swr);
	swr->enclave = e;	/* weak reference */

	/* XXX memcg charge */

	return swr;
}

static int ghost_prep_task(struct ghost_enclave *e, struct task_struct *p,
			   bool forked)
{
	int error;
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	error = __ghost_prep_task(e, p, e->def_q, forked);
	spin_unlock_irqrestore(&e->lock, irq_fl);

	return error;
}

/*
 * 'p' and 'rq' are both locked.
 */
static int ghost_prep_agent(struct ghost_enclave *e, struct task_struct *p,
			    struct rq *rq, struct ghost_queue *q)
{
	int ret = 0;

	lockdep_assert_held(&rq->lock);
	lockdep_assert_held(&p->pi_lock);

	WARN_ON_ONCE(!capable(CAP_SYS_NICE));

	/*
	 * Bail if the task wants to be an agent but there is already
	 * an agent associated with this runqueue.
	 */
	if (rq->ghost.agent != NULL)
		return -EBUSY;

	/*
	 * Clean up old transactions.  Once this cpu has an agent, an old
	 * transaction could succeed and turn into a latched task and start
	 * running.
	 *
	 * You may be wondering why we do this here in addition to when the old
	 * agent exited.  It's possible for a global agent from an older agent
	 * process to write a transaction *after* that cpu's agent task exited.
	 */
	ghost_claim_and_kill_txn(rq->cpu, GHOST_TXN_NO_AGENT);

	/* We hold the rq lock, which is already irqsaved. */
	spin_lock(&e->lock);

	if (!cpumask_test_cpu(rq->cpu, &e->cpus)) {
		ret = -ENODEV;
		goto out;
	}
	if (!q) {
		/*
		 * Agents typically pass in their own queue, but if not they get
		 * the def_q (typically for tests).  But they must have *some*
		 * queue.
		 */
		if (!e->def_q) {
			ret = -ENXIO;
			goto out;
		}
		q = e->def_q;
	}

	ret = __ghost_prep_task(e, p, q, /*forked=*/false);
	if (ret)
		goto out;

	p->ghost.agent = true;
	ghost_sw_set_flag(p->ghost.status_word, GHOST_SW_TASK_IS_AGENT);

	/*
	 * The agent is not in the ghost class yet, but it will be before the RQ
	 * lock is unlocked.
	 *
	 * We set this now so that if you hold the enclave lock and a cpu
	 * belongs to the enclave, then you can *inspect* that cpu's
	 * rq->ghost.agent.  Setting or clearing it requires both the enclave
	 * lock and the RQ lock.
	 */
	WARN_ON(rq->ghost.agent || rq->ghost.blocked_in_run);
	rq->ghost.agent = p;

out:
	spin_unlock(&e->lock);
	return ret;
}

static int _ghost_sched_fork(struct ghost_enclave *e, struct task_struct *p)
{
	return ghost_prep_task(e, p, true);
}

static void _ghost_sched_cleanup_fork(struct ghost_enclave *e,
				      struct task_struct *p)
{
	struct ghost_status_word *sw;
	struct ghost_queue *q;
	ulong flags;
	int error;

	VM_BUG_ON(!task_has_ghost_policy(p));
	VM_BUG_ON(e != p->ghost.enclave);
	VM_BUG_ON(e == NULL);

	/*
	 * Clear association between 'p' and the default queue.
	 */
	q = p->ghost.dst_q;
	if (q != NULL) {
		p->ghost.dst_q = NULL;
		queue_decref(q);
	} else {
		/*
		 * Although it is possible for a task to have a no 'dst_q'
		 * this is expected only for a task that setsched's into
		 * ghost. For the parent task to fork it must be running
		 * which means that the enclave was functional with the
		 * 'def_q' properly configured.
		 */
		WARN_ON_ONCE(true);
	}

	sw = p->ghost.status_word;
	if (sw != NULL) {
		VM_BUG_ON(!e);
		p->ghost.status_word = NULL;
		spin_lock_irqsave(&e->lock, flags);
		error = free_status_word_locked(e, sw);
		spin_unlock_irqrestore(&e->lock, flags);
		VM_BUG_ON(error);
	} else {
		WARN_ON_ONCE(true);	/* not expected */
	}

	if (e) {
		kref_put(&e->kref, enclave_release);
		p->ghost.enclave = NULL;
	} else {
		WARN_ON_ONCE(true);	/* not expected */
	}
}

/*
 * attr->sched_priority is *not* set by the user.  It is set by the ghostfs
 * commands that call setscheduler elsewhere in this file.  They aren't part of
 * any ABI.
 *
 * sched_priority is an argument from ghostfs to tell us if we're dealing with
 * an agent or not, and if so, which qfd it wants.
 *  < -1 : a regular task
 * == -1 : an agent, use the default queue
 * >=  0 : an agent, sched_priority is the fd for the queue.
 *
 * Anyone who calls sys_sched_setscheduler (or setattr) will not have a
 * target_enclave() set.
 */
static int _ghost_setscheduler(struct ghost_enclave *e, struct task_struct *p,
			       struct rq *rq, const struct sched_attr *attr,
			       int *reset_on_fork)
{
	int ret, qfd;

	if (WARN_ON_ONCE(!e))
		return -ENODEV;

	/* Task 'p' is departing the ghost sched class. */
	if (ghost_policy(p->policy)) {
		/*
		 * Don't allow an agent to move out of the ghost sched_class.
		 * There is no use case for this and more importantly we don't
		 * apply the side-effects of agent leaving the CPU (compare to
		 * _task_dead_ghost() where we do).
		 */
		if (p->ghost.agent)
			return -EPERM;

		invalidate_cached_tasks(rq, p);
		return 0;
	}

	/* Any setsched *into* ghost must have come from ghostfs. */
	if (WARN_ON_ONCE(!get_target_enclave()))
		return -ENODEV;

	qfd = (int)attr->sched_priority;
	if (qfd >= -1) {
		struct fd f_que = {0};
		struct ghost_queue *q = NULL;

		/*
		 * A thread can only make a task an agent if the thread has the
		 * CAP_SYS_NICE capability.
		 */
		if (!capable(CAP_SYS_NICE))
			return -EPERM;

		if (qfd != -1) {
			f_que = fdget(qfd);
			q = fd_to_queue(f_que);
			if (!q) {
				fdput(f_que);
				return -EBADF;
			}
		}

		/* It's OK to set reset_on_fork even if we fail. */
		*reset_on_fork = 1;
		ret = ghost_prep_agent(e, p, rq, q);

		if (qfd != -1)
			fdput(f_que);
	} else {
		ret = ghost_prep_task(e, p, false);
	}

	return ret;
}

/* Makes newq the default for e. */
static void enclave_set_default_queue(struct ghost_enclave *e,
				      struct ghost_queue *newq)
{
	unsigned long irq_fl;

	/*
	 * All queues belong to an enclave, and they can only be default for
	 * their enclave.
	 */
	if (WARN_ON(newq->enclave != e))
		return;

	spin_lock_irqsave(&e->lock, irq_fl);
	/*
	 * def_q is a weak (uncounted) reference.  We explicitly clear it in
	 * queue_release when q no longer tracks this enclave.  It is protected
	 * by the enclave lock.
	 */
	e->def_q = newq;
	spin_unlock_irqrestore(&e->lock, irq_fl);
}

/* Unsets q as default, if it was default. */
static void enclave_maybe_del_default_queue(struct ghost_enclave *e,
					    struct ghost_queue *q)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	if (e->def_q == q)
		e->def_q = NULL;
	spin_unlock_irqrestore(&e->lock, irq_fl);
}

static int queue_mmap(struct file *file, struct vm_area_struct *vma)
{
	struct ghost_queue *q = file->private_data;

	return ghost_region_mmap(file, vma, q->addr, q->mapsize);
}

static int queue_release(struct inode *inode, struct file *file)
{
	struct ghost_queue *q = file->private_data;
	struct ghost_enclave *e = q->enclave;

	enclave_maybe_del_default_queue(e, q);
	q->enclave = NULL;
	kref_put(&e->kref, enclave_release);
	queue_decref(q);		/* drop inode reference */
	return 0;
}

static const struct file_operations queue_fops = {
	.release		= queue_release,
	.mmap			= queue_mmap,
};

static int ghost_create_queue(struct ghost_enclave *e,
			      struct ghost_ioc_create_queue __user *arg)
{
	ulong size;
	int error = 0, fd, elems, node, flags;
	struct ghost_queue *q;
	struct ghost_queue_header *h;
	struct ghost_ioc_create_queue create_queue;

	const int valid_flags = 0;	/* no flags for now */

	if (copy_from_user(&create_queue, arg,
			   sizeof(struct ghost_ioc_create_queue)))
		return -EFAULT;

	elems = create_queue.elems;
	node = create_queue.node;
	flags = create_queue.flags;

	/*
	 * Validate that 'head' and 'tail' are large enough to distinguish
	 * between an empty and full queue. In other words when the queue
	 * goes from empty to full we want to guarantee that 'head' will
	 * not rollover 'tail'.
	 */
	BUILD_BUG_ON(
		GHOST_MAX_QUEUE_ELEMS >=
		    ((typeof(((struct ghost_ring *)0)->head))~0UL)
	);

	if (elems < 0 || elems > GHOST_MAX_QUEUE_ELEMS || !is_power_of_2(elems))
		return -EINVAL;

	if (flags & ~valid_flags)
		return -EINVAL;

	if (node < 0 || node >= nr_node_ids || !node_online(node))
		return -EINVAL;

	size = sizeof(struct ghost_queue_header) + sizeof(struct ghost_ring);
	size += elems * sizeof(struct ghost_msg);
	size = PAGE_ALIGN(size);

	error = put_user(size, &arg->mapsize);
	if (error)
		return error;

	q = kzalloc_node(sizeof(struct ghost_queue), GFP_KERNEL, node);
	if (!q) {
		error = -ENOMEM;
		return error;
	}

	spin_lock_init(&q->lock);
	kref_init(&q->kref); /* sets to 1; inode gets its own reference */
	q->addr = vmalloc_user_node_flags(size, node, GFP_KERNEL);
	if (!q->addr) {
		error = -ENOMEM;
		goto err_vmalloc;
	}

	h = q->addr;
	h->version = GHOST_QUEUE_VERSION;
	h->start = sizeof(struct ghost_queue_header);
	h->nelems = elems;

	/*
	 * The queue mapping is writeable so we cannot trust anything
	 * in the header after it is mapped by the agent.
	 *
	 * Stash a pointer to the ring and number of elements below.
	 */
	q->ring = (struct ghost_ring *)((char *)h + h->start);
	q->nelems = h->nelems;
	q->mapsize = size;

	fd = anon_inode_getfd("[ghost_queue]", &queue_fops, q,
			      O_RDWR | O_CLOEXEC);
	if (fd < 0) {
		error = fd;
		goto err_getfd;
	}

	kref_get(&e->kref);
	q->enclave = e;
	INIT_WORK(&q->free_work, __queue_free_work);

	return fd;

err_getfd:
	vfree(q->addr);
err_vmalloc:
	kfree(q);
	return error;
}

static struct task_struct *find_task_by_gtid(gtid_t gtid)
{
	struct task_struct *p;
	pid_t pid = gtid >> GHOST_TID_SEQNUM_BITS;

	RCU_LOCKDEP_WARN(!rcu_read_lock_held(),
			 "find_task_by_gtid() needs rcu_read_lock protection");

	if (gtid < 0)
		return NULL;

	if (gtid == 0)
		return current;

	p = find_task_by_pid_ns(pid, &init_pid_ns);

	/*
	 * It is possible for a task to schedule after losing its identity
	 * during exit (do_exit -> unhash_process -> detach_pid -> free_pid).
	 *
	 * Since the agent identifies tasks to schedule using a 'gtid' we
	 * must provide an alternate lookup path so the dying task can be
	 * scheduled and properly die.
	 */
	if (unlikely(!p)) {
		ulong flags;
		struct task_struct *t;
		struct ghost_enclave *e;

		e = rcu_dereference(per_cpu(enclave, smp_processor_id()));
		if (!e)
			return NULL;

		spin_lock_irqsave(&e->lock, flags);
		list_for_each_entry(t, &e->task_list, ghost.task_list) {
			if (t->gtid == gtid) {
				p = t;
				break;
			}
		}
		spin_unlock_irqrestore(&e->lock, flags);
	}
	if (!p)
		return NULL;

	/* Make sure this really is the process we are looking for. */
	if (p->gtid != gtid)
		return NULL;

	/*
	 * We rely on rcu to guarantee stability of 'p':
	 *
	 * If 'p' was obtained via find_task_by_pid_ns() then release_task()
	 * waits for an rcu grace period via call_rcu(delayed_put_task_struct).
	 * This includes the case where userspace moves a task out of ghost
	 * via sched_setscheduler(2).
	 *
	 * If 'p' was obtained via enclave->task_list then we need to account
	 * for the task dying or moving out of the ghost sched_class when its
	 * enclave is destroyed.
	 *
	 * A dying task ensures that the task_struct will remain stable for
	 * an rcu grace period via call_rcu(ghost_delayed_put_task_struct).
	 *
	 * A dying enclave will synchronize_rcu() in __ghost_destroy_enclave()
	 * before moving its tasks out of ghost (we don't use call_rcu() here
	 * because the task may transition in and out of ghost any number of
	 * times independent of call_rcu() invocation).
	 */
	return p;
}

static int _get_sw_info_locked(struct ghost_enclave *e,
			       const struct ghost_status_word *sw,
			       struct ghost_sw_info *info)
{
	int error = -ENOENT;
	struct ghost_sw_region *region;
	struct ghost_sw_region_header *header;
	struct ghost_status_word *first, *limit;

	VM_BUG_ON(!spin_is_locked(&e->lock));
	list_for_each_entry(region, &e->sw_region_list, list) {
		header = region->header;
		first = first_status_word(header);
		limit = &first[header->capacity];
		if (sw >= first && sw < limit) {
			info->id = header->id;
			info->index = sw - first;
			error = 0;	/* success */
			break;
		}
	}
	return error;
}

static int _get_sw_info(struct ghost_enclave *e,
			 const struct ghost_status_word *sw,
			 struct ghost_sw_info *info)
{
	ulong flags;
	int ret;

	spin_lock_irqsave(&e->lock, flags);
	ret = _get_sw_info_locked(e, sw, info);
	spin_unlock_irqrestore(&e->lock, flags);
	return ret;
}

static int ghost_sw_get_info(struct ghost_enclave *e,
			     struct ghost_ioc_sw_get_info __user *arg)
{
	int error = -EINVAL;
	struct task_struct *p;
	struct ghost_msg_src src;
	struct ghost_sw_info info = { 0 };

	if (copy_from_user(&src, &arg->request, sizeof(struct ghost_msg_src)))
		return -EFAULT;

	if (src.type == GHOST_AGENT) {
		ulong flags;
		int want_cpu = src.arg;
		struct rq *rq;
		struct task_struct *agent;

		/*
		 * A write must acquire both the enclave lock and the rq lock to
		 * write rq->ghost.agent, so it is safe to read rq->ghost.agent
		 * as long as we hold at least one of the two locks. We want to
		 * check that 'want_cpu' is in the enclave, so we may as well
		 * just acquire the enclave lock.
		 */
		spin_lock_irqsave(&e->lock, flags);

		/* Check that 'want_cpu' is in the enclave 'e'. */
		if (!cpumask_test_cpu(want_cpu, &e->cpus)) {
			error = -ENODEV;
			spin_unlock_irqrestore(&e->lock, flags);
			goto done;
		}

		rq = cpu_rq(want_cpu);
		agent = rq->ghost.agent;
		/*
		 * The agent may not have finished starting up yet or may have
		 * died already.
		 */
		if (unlikely(!agent)) {
			error = -EINVAL;
			spin_unlock_irqrestore(&e->lock, flags);
			goto done;
		}

		error = _get_sw_info_locked(e, agent->ghost.status_word,
					    &info);
		spin_unlock_irqrestore(&e->lock, flags);
	} else if (src.type == GHOST_TASK) {
		rcu_read_lock();
		p = find_task_by_gtid(src.arg);
		if (p && p->ghost.status_word)
			error = _get_sw_info(e, p->ghost.status_word, &info);
		else
			error = -ENOENT;
		rcu_read_unlock();
	}

	if (!error) {
		if (copy_to_user(&arg->response, &info,
				 sizeof(struct ghost_sw_info)))
			error = -EFAULT;
	}

done:
	return error;
}

static int ghost_sw_free(struct ghost_enclave *e,
			 struct ghost_sw_info __user *uinfo)
{
	int error;
	bool gated;
	gtid_t gtid;
	ulong flags;
	struct task_struct *p = NULL;
	struct ghost_status_word *sw;
	struct ghost_sw_info info = { 0 };

	if (copy_from_user(&info, uinfo, sizeof(struct ghost_sw_info)))
		return -EFAULT;

	spin_lock_irqsave(&e->lock, flags);

	sw = lookup_status_word_locked(e, info.id, info.index);
	if (sw == NULL) {
		error = -ENOENT;
		goto done;
	}
	if (!status_word_canfree(sw)) {
		error = -EINVAL;
		goto done;
	}
	gtid = sw->gtid;
	gated = sw->flags & GHOST_SW_TASK_MSG_GATED;
	error = free_status_word_locked(e, sw);
	if (!error && gated) {
		p = __enclave_remove_inhibited_task(e, gtid);
		WARN_ON_ONCE(!p);
	}
done:
	spin_unlock_irqrestore(&e->lock, flags);
	if (p)
		ghost_uninhibit_task_msgs(p);

	return error;
}

static int ghost_associate_queue(struct ghost_ioc_assoc_queue __user *arg)
{
	int error = 0;
	struct rq *rq;
	struct file *file;
	struct rq_flags rf;
	struct ghost_msg_src src;
	struct task_struct *p = NULL;
	struct ghost_status_word *sw;
	struct ghost_queue *oldq, *newq;
	int status = 0;

	int fd, barrier, flags;
	struct ghost_ioc_assoc_queue assoc_queue;

	if (copy_from_user(&assoc_queue, arg,
			   sizeof(struct ghost_ioc_assoc_queue)))
		return -EFAULT;

	fd = assoc_queue.fd;
	barrier = assoc_queue.barrier;
	flags = assoc_queue.flags;
	src = assoc_queue.src;

	if (flags != 0)			/* no flags for now */
		return -EINVAL;

	/* For now only allow changing task-to-queue association. */
	if (src.type != GHOST_TASK)
		return -EINVAL;

	file = fget(fd);
	if (!file)
		return -EBADF;

	if (file->f_op != &queue_fops) {
		error = -EBADF;
		goto done;
	}

	newq = file->private_data;

	rcu_read_lock();
	p = find_task_by_gtid(src.arg);
	if (!p) {
		rcu_read_unlock();
		error = -ENOENT;
		goto done;
	}

	/* Serialize with sched_setscheduler(), clone() and exit() */
	rq = task_rq_lock(p, &rf);
	rcu_read_unlock();

	oldq = p->ghost.dst_q;
	sw = p->ghost.status_word;
	if (unlikely(!sw)) {
		/* Task is dead or switched to another sched_class */
		WARN_ON_ONCE(p->state != TASK_DEAD &&
			     ghost_class(p->sched_class));
		error = -ENOENT;
		goto done;
	}

	if (barrier_get(p) != barrier) {
		error = -ESTALE;
		goto done;
	}

	/*
	 * Associating to the preexisting queue would be a noop, but telling
	 * userspace helps with in-place upgrade.  In particular, the agent
	 * knows whether or not it may have received messages for a task that
	 * joined the enclave after the agent set its default queue.
	 */
	if (oldq == newq)
		status |= GHOST_ASSOC_SF_ALREADY;
	/*
	 * If a running task was setsched into ghost by a third party, and it
	 * hasn't blocked or been preempted yet, then its TASK_NEW has not been
	 * sent.  That task may or may not have an assigned queue, so this is
	 * different than detecting oldq == newq.
	 */
	if (p->ghost.new_task)
		status |= GHOST_ASSOC_SF_BRAND_NEW;

	/*
	 * All task msgs may be inhibited (including TASK_NEW) because the
	 * agent hasn't finished handling TASK_DEPARTED from the previous
	 * incarnation. This is similar to 'p->ghost.new_task' check above
	 * in that TASK_NEW will be produced when the status_word from the
	 * earlier incarnation is freed.
	 */
	if (p->inhibit_task_msgs) {
		/*
		 * The status_word associated with the previous incarnation
		 * of the task is orphaned (it cannot be reached from any
		 * task struct) so we should never see the GATED flag in
		 * any "live" status_word.
		 */
		WARN_ON_ONCE(sw->flags & GHOST_SW_TASK_MSG_GATED);
		status |= GHOST_ASSOC_SF_BRAND_NEW;
	}

	queue_incref(newq);
	p->ghost.dst_q = newq;
	if (oldq)
		queue_decref(oldq);

done:
	if (p)
		task_rq_unlock(rq, p, &rf);
	fput(file);
	if (!error) {
		WARN_ON_ONCE(status < 0);
		return status;
	}

	return error;
}

static int ghost_set_default_queue(struct ghost_enclave *e,
			   struct ghost_ioc_set_default_queue __user *arg)
{
	int error = 0;
	struct fd f_que = {0};
	struct ghost_queue *newq;

	int qfd;
	struct ghost_ioc_set_default_queue set_queue;

	if (copy_from_user(&set_queue, arg,
			   sizeof(struct ghost_ioc_set_default_queue)))
		return -EFAULT;

	qfd = set_queue.fd;

	f_que = fdget(qfd);
	newq = fd_to_queue(f_que);
	if (!newq) {
		error = -EBADF;
		goto err_newq;
	}
	/*
	 * Make sure that 'newq' belongs to the same enclave as the one
	 * whose default queue we are updating.
	 */
	if (newq->enclave != e) {
		error = -EINVAL;
		goto err_newq;
	}
	enclave_set_default_queue(e, newq);

err_newq:
	fdput(f_que);
	return error;
}

/*
 * Resolve the target CPU associated with a ghost_queue.
 *
 * The caller must guarantee that 'q' is stable.
 *
 * For e.g. the ghost queue associated with a task (p->ghost.dst_q)
 * is protected by task_rq(p)->lock. It is the caller's responsibility
 * to hold the 'rq->lock' when target_cpu(p->ghost.dst_q) is called.
 *
 * Returns the CPU of the ghost agent to wakeup or -1 if an eligible
 * CPU is not found or configured.
 */
static int target_cpu(struct ghost_queue *q, int preferred_cpu)
{
	struct queue_notifier *notifier;
	int cpu = -1, i;

	if (unlikely(!q))
		return -1;

	rcu_read_lock();
	notifier = rcu_dereference(q->notifier);
	if (notifier) {
		VM_BUG_ON(notifier->wnum > GHOST_MAX_WINFO);
		for (i = 0; i < notifier->wnum; i++) {
			const int wakeup_cpu = notifier->winfo[i].cpu;

			if (cpu < 0)
				cpu = wakeup_cpu;

			/*
			 * If the preferred_cpu is one of the candidates then
			 * choose it. This is so that task state change msgs
			 * (e.g. TASK_BLOCKED) naturally wake the local agent.
			 */
			if (wakeup_cpu == preferred_cpu) {
				cpu = preferred_cpu;
				break;
			}
		}
	}
	rcu_read_unlock();
	return cpu;
}

static int task_target_cpu(struct task_struct *p)
{
	struct rq *rq = task_rq(p);

	/* 'p->ghost.dst_q' is protected by 'rq->lock' */
	lockdep_assert_held(&rq->lock);

	/*
	 * It doesn't make sense to notify an agent about its own state change.
	 */
	if (unlikely(p->ghost.agent))
		return -1;

	return target_cpu(p->ghost.dst_q, task_cpu(p));
}

static int agent_target_cpu(struct rq *rq)
{
	struct task_struct *agent = rq->ghost.agent;

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(!is_agent(rq, agent));

	return target_cpu(agent->ghost.dst_q, task_cpu(agent));
}

static int ghost_config_queue_wakeup(
		struct ghost_ioc_config_queue_wakeup __user *arg)
{
	struct ghost_queue *q;
	struct queue_notifier *old, *qn = NULL;
	struct ghost_agent_wakeup wakeup[GHOST_MAX_WINFO];
	struct file *f;
	ulong fl;
	int cpu = -1, i;
	int ret = 0;

	int qfd, ninfo, flags;
	struct ghost_agent_wakeup *w;
	struct ghost_ioc_config_queue_wakeup config_wakeup;

	if (copy_from_user(&config_wakeup, arg,
			   sizeof(struct ghost_ioc_config_queue_wakeup)))
		return -EFAULT;

	qfd = config_wakeup.qfd;
	w = config_wakeup.w;
	ninfo = config_wakeup.ninfo;
	flags = config_wakeup.flags;

	if (ninfo < 0 || ninfo > GHOST_MAX_WINFO)
		return -EINVAL;

	if (flags)
		return -EINVAL;

	f = fget(qfd);
	if (!f)
		return -EBADF;

	if (f->f_op != &queue_fops) {
		ret = -EBADF;
		goto out_fput;
	}

	q = f->private_data;
	if (!q) {
		ret = -EINVAL;
		goto out_fput;
	}

	if (ninfo) {
		if (copy_from_user(&wakeup, w,
				   sizeof(struct ghost_agent_wakeup) * ninfo)) {
			ret = -EFAULT;
			goto out_fput;
		}

		for (i = 0; i < ninfo; i++) {
			cpu = wakeup[i].cpu;

			if (wakeup[i].prio || cpu < 0 || cpu >= nr_cpu_ids ||
					   !cpu_online(cpu)) {
				ret = -EINVAL;
				goto out_fput;
			}
		}

		qn = kzalloc(sizeof(struct queue_notifier), GFP_KERNEL);
		memcpy(qn->winfo, wakeup, sizeof(qn->winfo));
		qn->wnum = ninfo;
	}

	spin_lock_irqsave(&q->lock, fl);
	old = rcu_dereference_protected(q->notifier, lockdep_is_held(&q->lock));
	rcu_assign_pointer(q->notifier, qn);
	spin_unlock_irqrestore(&q->lock, fl);

	/* Wakeup agent on new CPU, in case 'q' has pending messages. */
	ghost_wake_agent_on(cpu);

	if (old)
		kfree_rcu(old, rcu);
out_fput:
	fput(f);
	return ret;
}

static int ghost_get_cpu_time(struct ghost_ioc_get_cpu_time __user *arg)
{
	struct task_struct *p;
	u64 time;
	gtid_t gtid;

	if (copy_from_user(&gtid, &arg->gtid, sizeof(gtid_t)))
		return -EFAULT;

	rcu_read_lock();
	p = find_task_by_gtid(gtid);
	if (!p) {
		rcu_read_unlock();
		return -ESRCH;
	}
	time = task_sched_runtime(p);
	rcu_read_unlock();
	if (copy_to_user(&arg->runtime, &time, sizeof(u64)))
		return -EFAULT;
	return 0;
}

/*
 * 'ring_avail_slots' returns the available slots in the ring.
 *
 * More interestingly it splits the available slots into two contiguous
 * segments. The first one starts at 'ring->head' and extends all the
 * way to the end of the ring buffer. The second one starts at the
 * beginning of the ring buffer and extends up to 'ring->tail'.
 *
 * The producer can then use this information to decide where to place
 * a message. For e.g. assume that 'ring->head' is on the last slot of
 * an empty ring buffer (i.e. ring->tail == ring->head). If a message
 * requires two slots then the producer can skip the last slot with a
 * NOP message and enqueue the actual message in the first two slots
 * of the ring buffer.
 */
struct avail_slots {
	uint32_t ahead;		/* slots from 'head' to end of buffer */
	uint32_t behind;	/* slots from beginning of buffer to 'tail' */
};

static inline struct avail_slots
ring_avail_slots(struct ghost_ring *r, uint32_t maxslots)
{
	uint32_t used;
	uint32_t head, tail;
	struct avail_slots slots;

	head = READ_ONCE(r->head);
	tail = READ_ONCE(r->tail);
	used = head - tail;

	if (used >= maxslots) {
		/*
		 * Ring is full (bad) or head and tail are out-of-sync (worse).
		 *
		 * This deserves a WARN and we rely on the caller to do it
		 * because they have more context about the queue, msg etc.
		 */
		slots.ahead = slots.behind = 0;
	} else {
		uint32_t avail = maxslots - used;
		uint32_t hidx = head & (maxslots - 1);
		uint32_t tidx = tail & (maxslots - 1);

		if (tidx <= hidx) {
			slots.ahead = maxslots - hidx;
			slots.behind = tidx;
		} else {
			slots.ahead = tidx - hidx;
			slots.behind = 0;
		}
		VM_BUG_ON(avail != slots.ahead + slots.behind);
	}
	return slots;
}

static int _produce(struct ghost_queue *q, uint32_t barrier, int type,
		    void *payload, int payload_size)
{
	struct ghost_ring *ring = q->ring;
	uint32_t hidx, slots_needed, slots_skipped = 0;
	struct avail_slots avail;
	ulong flags;
	int msglen;

	const int nelems = q->nelems;
	const int slot_size = sizeof(struct ghost_msg);

	BUILD_BUG_ON_NOT_POWER_OF_2(slot_size);

	msglen = sizeof(struct ghost_msg) + payload_size;
	if (WARN_ON_ONCE(msglen > USHRT_MAX))
		return -EINVAL;
	slots_needed = ALIGN(msglen, slot_size) / slot_size;

	spin_lock_irqsave(&q->lock, flags);

	avail = ring_avail_slots(ring, nelems);
	if (WARN_ON_ONCE(avail.ahead < slots_needed &&
			 avail.behind < slots_needed)) {
		ring->overflow++;
		spin_unlock_irqrestore(&q->lock, flags);
		return -EOVERFLOW;
	}

	hidx = ring->head & (nelems - 1);
	if (unlikely(avail.ahead < slots_needed)) {
		/*
		 * Produce a NOP message to occupy all the slots up to
		 * the end of the ring buffer.
		 */
		ring->msgs[hidx].type = MSG_NOP;
		ring->msgs[hidx].length = avail.ahead * slot_size;

		/*
		 * Reset 'hidx' so we now produce starting from the
		 * beginning of the ring buffer.
		 */
		hidx = 0;
		slots_skipped = avail.ahead;
	}

	ring->msgs[hidx].type = type;
	ring->msgs[hidx].length = msglen;
	ring->msgs[hidx].seqnum = barrier;
	memcpy(&ring->msgs[hidx + 1], payload, payload_size);
	smp_wmb();	/* 'msg' update must be visible before 'head' update */

	ring->head += slots_skipped + slots_needed;
	smp_wmb();	/* publish the new message */

	spin_unlock_irqrestore(&q->lock, flags);

	return 0;
}


static inline int __produce_for_task(struct task_struct *p,
				     struct bpf_ghost_msg *msg,
				     uint32_t barrier)
{
	void *payload;
	int payload_size;

	msg->seqnum = barrier;

	switch (msg->type) {
	case MSG_TASK_DEAD:
		payload = &msg->dead;
		payload_size = sizeof(msg->dead);
		break;
	case MSG_TASK_BLOCKED:
		payload = &msg->blocked;
		payload_size = sizeof(msg->blocked);
		break;
	case MSG_TASK_WAKEUP:
		payload = &msg->wakeup;
		payload_size = sizeof(msg->wakeup);
		break;
	case MSG_TASK_NEW:
		payload = &msg->newt;
		payload_size = sizeof(msg->newt);
		break;
	case MSG_TASK_PREEMPT:
		payload = &msg->preempt;
		payload_size = sizeof(msg->preempt);
		break;
	case MSG_TASK_YIELD:
		payload = &msg->yield;
		payload_size = sizeof(msg->yield);
		break;
	case MSG_TASK_DEPARTED:
		payload = &msg->departed;
		payload_size = sizeof(msg->departed);
		break;
	case MSG_TASK_SWITCHTO:
		payload = &msg->switchto;
		payload_size = sizeof(msg->switchto);
		break;
	case MSG_TASK_AFFINITY_CHANGED:
		payload = &msg->affinity;
		payload_size = sizeof(msg->affinity);
		break;
	case MSG_TASK_LATCHED:
		payload = &msg->latched;
		payload_size = sizeof(msg->latched);
		break;
	case MSG_CPU_TICK:
		payload = &msg->cpu_tick;
		payload_size = sizeof(msg->cpu_tick);
		break;
	case MSG_CPU_TIMER_EXPIRED:
		payload = &msg->timer;
		payload_size = sizeof(msg->timer);
		break;
	case MSG_CPU_NOT_IDLE:
		payload = &msg->cpu_not_idle;
		payload_size = sizeof(msg->cpu_not_idle);
		break;
	default:
		WARN(1, "unknown bpg_ghost_msg type %d!\n", msg->type);
		return -EINVAL;
	};
	if (!ghost_bpf_msg_send(p->ghost.enclave, msg))
		return -ENOMSG;
	return _produce(p->ghost.dst_q, barrier, msg->type,
			payload, payload_size);
}

static inline int produce_for_task(struct task_struct *p,
				   struct bpf_ghost_msg *msg)
{
	return __produce_for_task(p, msg, task_barrier_get(p));
}

static inline int produce_for_agent(struct rq *rq,
				    struct bpf_ghost_msg *msg)
{
	struct task_struct *agent = rq->ghost.agent;

	agent_barrier_inc(rq);
	return __produce_for_task(agent, msg, agent_barrier_get(agent));
}

/*
 * There is a unique agent associated with each ghost CPU so we use
 * the agent as a proxy for delivering CPU messages (specifically
 * the 'dst_q' configuration). Not only is this convenient but the
 * 'status_word.barrier' increment in produce_for_agent() pairs
 * correctly with the 'agent_barrier' check in ghost_run().
 *
 * CPU messages are produced with the 'rq' lock held to serialize
 * with agent death and 'dst_q' changes via ghost_associate_queue().
 */
static inline bool cpu_skip_message(struct rq *rq)
{
	struct task_struct *agent = rq->ghost.agent;

	lockdep_assert_held(&rq->lock);

	if (WARN_ON_ONCE(!agent))
		return true;

	if (WARN_ON_ONCE(!agent->ghost.dst_q))
		return true;

	return false;
}

static inline bool cpu_deliver_msg_tick(struct rq *rq)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_cpu_tick *payload = &msg->cpu_tick;
	struct ghost_enclave *e;

	if (cpu_skip_message(rq))
		return false;
	rcu_read_lock();
	e = rcu_dereference(per_cpu(enclave, cpu_of(rq)));
	if (!e || !e->deliver_ticks) {
		rcu_read_unlock();
		return false;
	}
	rcu_read_unlock();

	msg->type = MSG_CPU_TICK;
	payload->cpu = cpu_of(rq);

	return !produce_for_agent(rq, msg);
}

/* Returns true if MSG_CPU_TIMER_EXPIRED was produced and false otherwise */
static inline bool cpu_deliver_timer_expired(struct rq *rq, uint64_t type,
					     uint64_t cookie)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_timer *payload = &msg->timer;

	if (cpu_skip_message(rq))
		return false;

	msg->type = MSG_CPU_TIMER_EXPIRED;
	payload->cpu = cpu_of(rq);
	payload->type = type;
	payload->cookie = cookie;

	return !produce_for_agent(rq, msg);
}

static bool cpu_deliver_msg_not_idle(struct rq *rq, struct task_struct *next)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_cpu_not_idle *payload = &msg->cpu_not_idle;

	if (cpu_skip_message(rq))
		return false;

	msg->type = MSG_CPU_NOT_IDLE;
	payload->cpu = cpu_of(rq);
	payload->next_gtid = gtid(next);

	return !produce_for_agent(rq, msg);
}

/*
 * When called from pick_next_task() context returns 'true' if 'rq->cpu'
 * is exiting switchto and 'false' otherwise (e.g. when producing the
 * TASK_BLOCKED/TASK_YIELD/TASK_PREEMPT msgs).
 *
 * When called outside pick_next_task() context returns 'true' if 'rq->cpu'
 * is currently in a switchto chain and 'false' otherwise (e.g. when producing
 * TASK_DEPARTED msg for an oncpu ghost task).
 *
 * Technically this could be split into two APIs one for 'switchto_count < 0'
 * and another for 'switchto_count > 0' but that feels like overkill.
 */
static bool ghost_in_switchto(struct rq *rq)
{
	return rq->ghost.switchto_count ? true : false;
}

/*
 * Returns 0 if we should produce a message for the task, < 0 otherwise.
 *
 * If the task is not an agent, this will task_barrier_inc(), even if we should
 * not produce a message.
 */
static inline int __task_deliver_common(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);

	/*
	 * Some operations (e.g. sched_setaffinity()) can race with task death
	 * in which case the 'status_word' is off limits and will cause an oops
	 * in task_barrier_inc() below.
	 */
	if (unlikely(!p->ghost.status_word)) {
		WARN_ON_ONCE(p->state != TASK_DEAD);
		return -1;
	}

	/*
	 * Ignore the agent's task_state changes.
	 *
	 * If the agent is not runnable then how do we tell it that
	 * it's not runnable.
	 */
	if (unlikely(is_agent(rq, p)))
		return -1;

	/*
	 * There should not be any deferred TASK_NEW at this point so WARN
	 * and proceed. The agent will also flag that it received a msg from
	 * an unknown task which is useful in case kernel log is unavailable.
	 * (for e.g. see b/193059731).
	 */
	WARN_ON_ONCE(p->ghost.new_task);

	/*
	 * Increment the barrier even if we are not going to send a message due
	 * to a missing queue, since the barrier protects some parts of the SW's
	 * state.
	 *
	 * Normally, this would be unsafe, since the barrier technically
	 * protects the messages, and userspace could be confused because it
	 * sees the barrier, but cannot see the message.  However, since p has
	 * no dst_q, it has not been associated yet, which means no scheduler
	 * is operating on it.  This can happen if a task arrives before an
	 * agent sets the enclave's default queue.  The agent will associate
	 * that task during task Discovery.
	 */
	task_barrier_inc(rq, p);

	if (!p->ghost.dst_q)
		return -1;

	/*
	 * Inhibit tasks msgs until agent acknowledges receipt of an earlier
	 * TASK_DEPARTED (by freeing the task's status_word). This ensures
	 * that msgs belonging to the previous incarnation of the task are
	 * drained before any msg from its current incarnation is produced.
	 */
	if (p->inhibit_task_msgs)
		return -1;

	return 0;
}

static void task_deliver_msg_task_new(struct rq *rq, struct task_struct *p,
				      bool runnable)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_new *payload = &msg->newt;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_NEW;
	payload->gtid = gtid(p);
	payload->runnable = runnable;
	payload->runtime = p->se.sum_exec_runtime;
	if (_get_sw_info(p->ghost.enclave, p->ghost.status_word,
			 &payload->sw_info)) {
		WARN(1, "New task PID %d didn't have a status word!", p->pid);
		return;
	}

	produce_for_task(p, msg);
}

static void task_deliver_msg_yield(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_yield *payload = &msg->yield;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_YIELD;
	payload->gtid = gtid(p);
	payload->runtime = p->se.sum_exec_runtime;
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;
	payload->agent_data = 0;
	payload->from_switchto = ghost_in_switchto(rq);

	produce_for_task(p, msg);
}

static void task_deliver_msg_preempt(struct rq *rq, struct task_struct *p,
				     bool from_switchto, bool was_latched)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_preempt *payload = &msg->preempt;

	if (__task_deliver_common(rq, p))
		return;

	/*
	 * It doesn't make sense to produce a TASK_PREEMPT while a switchto
	 * chain is active.
	 *
	 * Stated differently TASK_PREEMPT is only expected when:
	 * 1. the task is not part of an active switchto chain:
	 *    - a task that got oncpu via __schedule().
	 *    - a latched_task.
	 * 2. the task was in an active switchto chain that is now broken:
	 *    - preempted by a higher priority sched_class.
	 *    - preempted by the agent doing a transaction commit.
	 */
	WARN_ON_ONCE(from_switchto && rq->ghost.switchto_count > 0);

	msg->type = MSG_TASK_PREEMPT;
	payload->gtid = gtid(p);
	payload->runtime = p->se.sum_exec_runtime;
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;
	payload->agent_data = 0;
	payload->from_switchto = from_switchto;
	payload->was_latched = was_latched;

	produce_for_task(p, msg);
}

static void task_deliver_msg_blocked(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_blocked *payload = &msg->blocked;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_BLOCKED;
	payload->gtid = gtid(p);
	payload->runtime = p->se.sum_exec_runtime;
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;
	payload->from_switchto = ghost_in_switchto(rq);

	produce_for_task(p, msg);
}

static bool task_deliver_msg_dead(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_dead *payload = &msg->dead;

	if (__task_deliver_common(rq, p))
		return false;

	msg->type = MSG_TASK_DEAD;
	payload->gtid = gtid(p);
	return produce_for_task(p, msg) == 0;
}

static bool task_deliver_msg_departed(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_departed *payload = &msg->departed;

	if (__task_deliver_common(rq, p))
		return false;

	msg->type = MSG_TASK_DEPARTED;
	payload->gtid = gtid(p);
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;
	if (task_current(rq, p) && ghost_in_switchto(rq))
		payload->from_switchto = true;
	else
		payload->from_switchto = false;
	payload->was_current = task_current(rq, p);

	return produce_for_task(p, msg) == 0;
}

static void task_deliver_msg_affinity_changed(struct rq *rq,
					      struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_affinity_changed *payload =
		&msg->affinity;

	/*
	 * A running task can be switched into ghost while it is executing
	 * sched_setaffinity. In this case the TASK_NEW msg is held pending
	 * until the task schedules and producing the TASK_AFFINITY_CHANGED
	 * msg is useless at best since the agent has no idea about this task.
	 */
	if (unlikely(p->ghost.new_task))
		return;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_AFFINITY_CHANGED;
	payload->gtid = gtid(p);

	produce_for_task(p, msg);
}

static void task_deliver_msg_latched(struct rq *rq, struct task_struct *p,
				     bool latched_preempt)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_latched *payload = &msg->latched;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_LATCHED;
	payload->gtid = gtid(p);
	payload->commit_time = ktime_get_ns();
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;
	payload->latched_preempt = latched_preempt;

	produce_for_task(p, msg);
}

static inline bool deferrable_wakeup(struct task_struct *p)
{
#ifdef notyet
	/*
	 * If 'p' held a lock while it was blocked then the wakeup
	 * is not deferrable since other tasks might be waiting on it.
	 */
	if (p->lockdep_depth)
		return false;
#endif

	return p->sched_deferrable_wakeup;
}

static void task_deliver_msg_wakeup(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_wakeup *payload = &msg->wakeup;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_WAKEUP;
	payload->gtid = gtid(p);
	payload->agent_data = 0;
	payload->deferrable = deferrable_wakeup(p);
	payload->last_ran_cpu = p->ghost.twi.last_ran_cpu;
	payload->wake_up_cpu = p->ghost.twi.wake_up_cpu;
	payload->waker_cpu = p->ghost.twi.waker_cpu;

	produce_for_task(p, msg);
}

static void task_deliver_msg_switchto(struct rq *rq, struct task_struct *p)
{
	struct bpf_ghost_msg *msg = &per_cpu(bpf_ghost_msg, cpu_of(rq));
	struct ghost_msg_payload_task_switchto *payload = &msg->switchto;

	if (__task_deliver_common(rq, p))
		return;

	msg->type = MSG_TASK_SWITCHTO;
	payload->gtid = gtid(p);
	payload->runtime = p->se.sum_exec_runtime;
	payload->cpu = cpu_of(rq);
	payload->cpu_seqnum = ++rq->ghost.cpu_seqnum;

	produce_for_task(p, msg);
}

static void release_from_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_enclave *e = p->ghost.enclave;
	ulong flags;

	VM_BUG_ON(!e);

	lockdep_assert_held(&rq->lock);
	lockdep_assert_held(&p->pi_lock);

	WARN_ON_ONCE(is_cached_task(rq, p));
	WARN_ON_ONCE(p->ghost.new_task);

	spin_lock_irqsave(&e->lock, flags);

	/* Remove before potentially clearing p->ghost.agent. */
	__enclave_remove_task(e, p);

	if (p->inhibit_task_msgs) {
		/*
		 * Agent is not going to free the status_word since it
		 * never saw any msgs associated with this incarnation:
		 * 1. p->state != TASK_DEAD (task departed)
		 *    task departed, came back into ghost and departed again
		 *    before agent had a chance to handle the first DEPARTED.
		 * 2. p->state == TASK_DEAD (task is dead)
		 *    task departed and came back into ghost while exiting
		 *    before agent had a chance to handle the DEPARTED msg.
		 */
		free_status_word_locked(e, p->ghost.status_word);
	} else if (p->state != TASK_DEAD) {
		/* agents cannot setsched out of ghost */
		WARN_ON_ONCE(is_agent(rq, p));

		ghost_sw_set_flag(p->ghost.status_word,
				  GHOST_SW_F_CANFREE|GHOST_SW_TASK_MSG_GATED);
		if (!task_deliver_msg_departed(rq, p)) {
			free_status_word_locked(e, p->ghost.status_word);
		} else {
			/*
			 * Inhibit all msgs produced by this task until the
			 * agent acknowledges receipt of TASK_DEPARTED msg
			 * (implicitly by freeing the status_word). This ensures
			 * that when TASK_NEW is produced any msgs associated
			 * with an earlier incarnation have been consumed.
			 */
			p->inhibit_task_msgs = enclave_abi(e);

			/*
			 * Track the task in the enclave's
			 * 'inhibited_task_list'.
			 *
			 * We must do this because a departed task can re-enter
			 * ghost while it is exiting and subsequently lose its
			 * identity (e.g. see go/kcl/390722). It is possible for
			 * the task to enter a different enclave in which case
			 * the fallback in kcl/390722 is ineffective.
			 *
			 * TODO: declare enclave failure if agent does not free
			 * the status_word of a departed task within X msec (X
			 * should be smaller than the e->max_unscheduled
			 * timeout):
			 * - misbehavior of one enclave should not result in a
			 *   (false-positive) failure of a different enclave.
			 * - limit the task_struct memory held hostage while
			 *   they are on the inhibited_task_list.
			 */
			get_task_struct(p);
			WARN_ON_ONCE(!list_empty(&p->inhibited_task_list));
			list_add_tail(&p->inhibited_task_list,
				      &e->inhibited_task_list);
		}
	} else {
		/*
		 * Annotate the status_word so it can be freed by the agent.
		 *
		 * N.B. this must be ordered before the TASK_DEAD message is
		 * visible to the agent.
		 *
		 * N.B. we grab the enclave lock to prevent a misbehaving agent
		 * from freeing the status_word (or its enclosing sw_region)
		 * before delivery of the TASK_DEAD message below.
		 */
		ghost_sw_set_flag(p->ghost.status_word, GHOST_SW_F_CANFREE);
		/*
		 * Automatically free the status_word if we didn't deliver a
		 * TASK_MSG_DEAD but only for non-agent ghost tasks.
		 *
		 * Otherwise, userspace will spin-wait for GHOST_SW_F_CANFREE as
		 * a sign that the agent fully exited, and then it destroys the
		 * SW.
		 */
		if (!task_deliver_msg_dead(rq, p) && !is_agent(rq, p))
			free_status_word_locked(e, p->ghost.status_word);
	}

	/* status_word is off-limits to the kernel */
	p->ghost.status_word = NULL;

	if (unlikely(is_agent(rq, p))) {
		/*
		 * Unlatched any tasks that had been committed.  Latched tasks
		 * will be selected in PNT after a new agent attaches, which
		 * violates the quiescence needed by in-place agent handoffs.
		 * Now that ghost.agent is NULL, any new transactions will fail.
		 *
		 * If the only concern is running a latched task, we could wait
		 * to clear latched_task until a new agent attaches, since PNT
		 * won't pick the latched_task unless there is an agent.
		 * However, it's possible that the agent process is trying to
		 * shrink its enclave: stop the agent, then remove the cpu,
		 * without killing the entire agent.  So we might never attach
		 * an old agent.  This is also why we use a preemption instead
		 * of invalidate_cached_tasks: preempt the committed task and
		 * let the agent (if there is one) handle it.
		 */
		if (rq->ghost.latched_task)
			ghost_latched_task_preempted(rq);
		/* We don't allow agents to setsched away from ghost */
		WARN_ON_ONCE(p->state != TASK_DEAD);
		rq->ghost.agent = NULL;
		/*
		 * Clear run_flags after dealing with latched_task: the
		 * run_flags pertain to the latched_task, especially for
		 * SEND_TASK_LATCHED.
		 */
		rq->ghost.run_flags = 0;
		WRITE_ONCE(rq->ghost.agent_barrier, 0);
		p->ghost.agent = false;
		VM_BUG_ON(rq->ghost.blocked_in_run);
		/*
		 * In case the user left some value that the next enclave could
		 * hit.
		 */
		WRITE_ONCE(rq->ghost.prev_resched_seq, ~0ULL);

		/*
		 * Clean up any pending transactions.  We need to do this here,
		 * in addition to in setsched, since the global agent may be
		 * spinning waiting for this transaction to return before it
		 * gracefully exits.
		 */
		ghost_claim_and_kill_txn(rq->cpu, GHOST_TXN_NO_AGENT);

		/* See __ghost_destroy_enclave() */
		if (p->ghost.__agent_decref_enclave) {
			/* Agents should only exit, never setsched out. */
			WARN_ON_ONCE(p->state != TASK_DEAD);
			VM_BUG_ON(p->ghost.__agent_decref_enclave != e);
			__enclave_remove_cpu(e, rq->cpu);
			/*
			 * At this moment, this cpu can be added to a new
			 * enclave (or our previous enclave!).
			 *
			 * Additionally, once we unlock the rq, a new agent task
			 * can attach to this cpu and use the rq->ghost fields.
			 *
			 * We've set pcpu->enclave = NULL (step 1).  Steps 2 and
			 * 3 (sync rcu and decref) are handled when we return to
			 * _task_dead_ghost() call_rcu.
			 */
		}
	}

	/*
	 * Will drop the kref for p->ghost.enclave, possibly as soon as we drop
	 * rq and e locks.
	 */
	submit_enclave_work(e, rq, false, /*nr_decrefs=*/ 1);
	p->ghost.enclave = NULL;

	spin_unlock_irqrestore(&e->lock, flags);

	ghost_wake_agent_of(p);

	/* Release reference to 'dst_q' */
	if (p->ghost.dst_q) {
		queue_decref(p->ghost.dst_q);
		p->ghost.dst_q = NULL;
	}
}

static void ghost_delayed_put_task_struct(struct rcu_head *rhp)
{
	struct task_struct *tsk = container_of(rhp, struct task_struct,
					       ghost.rcu);
	/*
	 * Step 3 of "destroyed with agent": decref.
	 * See __ghost_destroy_enclave().
	 */
	if (tsk->ghost.__agent_decref_enclave) {
		kref_put(&tsk->ghost.__agent_decref_enclave->kref,
			 enclave_release);
	}
	put_task_struct(tsk);
}

static void _task_dead_ghost(struct task_struct *p)
{
	struct rq_flags rf;
	struct rq *rq;
	struct callback_head *head;

	WARN_ON_ONCE(preemptible());

	rq = task_rq_lock(p, &rf);
	release_from_ghost(rq, p);
	head = splice_balance_callbacks(rq);
	task_rq_unlock(rq, p, &rf);

	/*
	 * 'p' is dead and the last reference to its task_struct may be
	 * dropped after returning from this function (see finish_task_switch).
	 *
	 * We need to drain all rcu-protected callers of find_task_by_gtid()
	 * before returning from this function. Typically this would happen
	 * via delayed_put_task_struct() called by release_task() but since
	 * we provide an alternate gtid lookup that bypasses find_task_by_pid()
	 * we cannot rely on that.
	 *
	 * Note that we cannot call synchronize_rcu() directly because this
	 * function is called in a non-preemptible context.
	 */
	get_task_struct(p);
	call_rcu(&p->ghost.rcu, ghost_delayed_put_task_struct);

	/*
	 * 'rq_pin_lock' issues a warning when the there are pending callback
	 * functions for the runqueue. The point of this warning is to ensure
	 * that callbacks are run in a timely manner
	 * (https://lkml.org/lkml/2020/9/11/1027).
	 *
	 * When 'release_from_ghost' adds a callback to the balance queue in the
	 * task_dead path, there is no subsequent call to 'balance_callbacks'
	 * before 'rq_pin_lock' is called. This causes the warning to be issued.
	 *
	 * To avoid the warning, we manually call 'balance_callbacks' here.
	 */
	balance_callbacks(rq, head);
}

/*
 * Update the scheduling state used by pick_next_task_ghost().
 */
static void ghost_set_pnt_state(struct rq *rq, struct task_struct *p,
				int run_flags)
{
	trace_sched_ghost_latched(rq->ghost.latched_task, p, run_flags);

	lockdep_assert_held(&rq->lock);

	if (rq->ghost.latched_task && rq->ghost.latched_task != p) {
		/*
		 * We're overwriting a 'latched_task' that never got oncpu.
		 * From the agent's perspective, this is a preemption, even if
		 * it is one that the agent implicitly requested by scheduling p
		 * onto this cpu to replace latched_task.  Contrast this to
		 * invalidate_cached_tasks(), which moves p from one cpu to
		 * another.
		 */
		ghost_latched_task_preempted(rq);
	}
	rq->ghost.latched_task = p;
	rq->ghost.must_resched = false;
	rq->ghost.run_flags = run_flags;

	/*
	 * Even though we don't send a message, this is a change in cpu state.
	 * When we later send TASK_LATCHED, that will increment again.
	 */
	rq->ghost.cpu_seqnum++;
}

/*
 * The essence of waking an agent: increment the barrier, regardless of if it
 * was sleeping, to ensure we catch the agent while it is attempting to block
 * (it will return ESTALE).
 *
 * If it was blocked_in_run, clear it and reschedule, which ensures it wakes up.
 *
 * Returns 0 on success, -error on failure.
 */
static int __ghost_wake_agent_on(int cpu, int this_cpu,
				 bool check_caller_enclave)
{
	struct rq *dst_rq;

	if (cpu < 0)
		return -EINVAL;
	if (cpu >= nr_cpu_ids || !cpu_online(cpu))
		return -ERANGE;

	if (check_caller_enclave && !check_same_enclave(this_cpu, cpu))
		return -EXDEV;

	dst_rq = cpu_rq(cpu);

	/*
	 * This is not the SW barrier.  The RQ agent_barrier can get ahead of
	 * the SW barrier, so we'll need to update the SW for userspace to see
	 * this update.
	 *
	 * agent_barrier_inc() holds the RQ lock and can clobber this increment.
	 * It's OK for us if *this* increment is lost.  We just need *some*
	 * increment to happen to prevent the agent from sleeping.  However, our
	 * update probably needs to be atomic.  If we do a non-atomic increment,
	 * it's possible for us to clobber agent_barrier_inc()'s locked update,
	 * and essentially rollback an agent barrier - possibly after it's been
	 * exposed to userspace.
	 *
	 * This sync operation is a full barrier.  This write must happen before
	 * the read of blocked_in_run.
	 */
	(void)__sync_fetch_and_add(&dst_rq->ghost.agent_barrier, 1);

	/*
	 * The barrier ordered this read already.  The READ_ONCE is harmless and
	 * mostly for paranoia.
	 */
	if (!READ_ONCE(dst_rq->ghost.blocked_in_run))
		return 0;

	/*
	 * We can't write blocked_in_run, since we don't hold the RQ lock.
	 * Instead, we'll tell the cpu to do it in pick_next_task (agent), by
	 * setting agent_should_wake and kicking the cpu.  The initial READ is
	 * an optimization to reduce the number of rescheds.
	 */
	if (READ_ONCE(dst_rq->ghost.agent_should_wake))
		return 0;
	WRITE_ONCE(dst_rq->ghost.agent_should_wake, true);

	/* Write must come before the IPI/resched */
	smp_wmb();

	if (cpu == this_cpu) {
		set_tsk_need_resched(dst_rq->curr);
		set_preempt_need_resched();
	} else {
		resched_cpu_unlocked(cpu);
	}
	return 0;
}

static void ghost_wake_agent_on(int cpu)
{
	int this_cpu = get_cpu();

	__ghost_wake_agent_on(cpu, this_cpu, /*check_caller_enclave=*/ false);
	put_cpu();
}

static int ghost_wake_agent_on_check(int cpu)
{
	int this_cpu = get_cpu();
	int ret;

	ret = __ghost_wake_agent_on(cpu, this_cpu,
				    /*check_caller_enclave=*/ true);
	put_cpu();
	return ret;
}

static void ghost_wake_agent_of(struct task_struct *p)
{
	ghost_wake_agent_on(task_target_cpu(p));
}

static void _ghost_task_preempted(struct rq *rq, struct task_struct *p,
				  bool was_latched)
{
	bool from_switchto;

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	/*
	 * When TASK_PREEMPTED is produced before returning from pick_next_task
	 * (e.g. via pick_next_ghost_agent) we don't have an up-to-date runtime
	 * since put_prev_task() hasn't been called yet.
	 *
	 * Therefore if 'p == rq->curr' we must do _update_curr_ghost() by hand.
	 */
	if (p == rq->curr)
		_update_curr_ghost(rq);

	/*
	 * If a latched task was preempted then by definition it was not
	 * part of any switchto chain.
	 */
	from_switchto = was_latched ? false : ghost_in_switchto(rq);

	/* Produce MSG_TASK_PREEMPT into 'p->ghost.dst_q' */
	task_deliver_msg_preempt(rq, p, from_switchto, was_latched);

	/*
	 * Wakeup agent on this CPU.
	 *
	 * In some scheduling models (e.g. uber-agent) this may be unnecessary
	 * and cause redundant context switches to the agent.
	 *
	 * Return to local agent if it has expressed interest in this edge.
	 */
	if (rq->ghost.run_flags & RTLA_ON_PREEMPT)
		schedule_agent(rq, false);
}

static void ghost_task_preempted(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	_ghost_task_preempted(rq, p, false);
}

static void ghost_task_got_oncpu(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	/*
	 * We must defer sending TASK_LATCHED until any prev ghost tasks got off
	 * cpu.  Otherwise the agent will have a hard time reconciling the
	 * current cpu state.
	 */
	if (rq->ghost.run_flags & SEND_TASK_LATCHED) {
		task_deliver_msg_latched(rq, p, false);
		/* Do not send the message more than once per commit. */
		rq->ghost.run_flags &= ~SEND_TASK_LATCHED;
	}
}

static void _ghost_task_new(struct rq *rq, struct task_struct *p, bool runnable)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	enclave_add_task(p->ghost.enclave, p);

	/* See explanation in ghost_task_preempted() */
	if (p == rq->curr)
		_update_curr_ghost(rq);

	task_deliver_msg_task_new(rq, p, runnable);
}

static void ghost_task_new(struct rq *rq, struct task_struct *p)
{
	_ghost_task_new(rq, p, task_on_rq_queued(p));
}

static void ghost_task_yield(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	/* See explanation in ghost_task_preempted() */
	if (p == rq->curr)
		_update_curr_ghost(rq);

	task_deliver_msg_yield(rq, p);
}

static void ghost_task_blocked(struct rq *rq, struct task_struct *p)
{
	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(task_rq(p) != rq);

	task_deliver_msg_blocked(rq, p);
}

static void wait_for_rendezvous(struct rq *rq)
{
	int64_t target;

	WARN_ON_ONCE(preemptible());

	/* agent does not rendezvous with anybody */
	if (is_agent(rq, rq->curr))
		return;

	while (!need_resched()) {
		target = smp_load_acquire(&rq->ghost.rendezvous);
#ifdef CONFIG_DEBUG_GHOST
		if (target == GHOST_NO_RENDEZVOUS)
			WARN_ON_ONCE(!need_resched());
#endif
		if (rendezvous_reached(target)) {
			/*
			 * Reschedule immediately if rendezvous is poisoned
			 * (some other txn in the sync_group failed to commit).
			 */
			if (unlikely(rendezvous_poisoned(target))) {
				struct rq_flags rf;
				/*
				 * We could race with a remote cpu doing a sync
				 * commit while waiting for rendezvous. This is
				 * usually not a problem because a successful
				 * commit results in an IPI to remote CPUs to
				 * apply the new scheduling state (except when
				 * the task is already running on the remote
				 * cpu in which case we elide the IPI).
				 *
				 * In cases where we don't get an IPI we have
				 * take care to not clobber updated scheduling
				 * state. For e.g. T1 started running on CPU1
				 * but its rendezvous was poisoned (another
				 * cpu in its sync_group failed to commit). By
				 * the time T1 acquired the rq->lock there was
				 * newer sync_group commit that committed T1
				 * on CPU1 (this one was successful). The new
				 * commit would detect that T1 was already on
				 * CPU1 and elide the IPI. Thus we check for
				 * poisoned rendezvous under 'rq->lock' lest
				 * we force T1 offcpu inadvertently!
				 */
				rq_lock_irqsave(rq, &rf);

				/*
				 * Validate everything after acquiring rq->lock
				 * since everything (including our sched_class)
				 * could have changed underneath us.
				 */
				if (!ghost_need_rendezvous(rq)) {
					rq_unlock_irqrestore(rq, &rf);
					return;
				}

				target = smp_load_acquire(
						&rq->ghost.rendezvous);
				if (!rendezvous_poisoned(target)) {
					rq_unlock_irqrestore(rq, &rf);
					continue;
				}
				_force_offcpu(rq,
					      /*resched=*/true,
					      /*ignore_prev_preemption=*/true);
				rq_unlock_irqrestore(rq, &rf);
				VM_BUG_ON(!need_resched());
			}
			break;
		}

		cpu_relax();
	}
}

static inline bool same_process(struct task_struct *p, struct task_struct *q)
{
	return p->group_leader == q->group_leader;
}

/*
 * Checks that the run flags are valid for a ghOSt txn or a ghost_run syscall.
 */
static inline bool run_flags_valid(int run_flags, int valid_run_flags,
				   gtid_t gtid)
{
	if (run_flags & ~valid_run_flags)
		return false;

	/*
	 * RTLA_ON_IDLE can be combined with GHOST_NULL_GTID (which is equal to
	 * 0), but should not be combined with any other special GTIDs.
	 */
	BUILD_BUG_ON(GHOST_NULL_GTID != 0);
	if ((run_flags & RTLA_ON_IDLE) && gtid < 0)
		return false;

	if ((run_flags & NEED_CPU_NOT_IDLE) && (gtid != GHOST_IDLE_GTID))
		return false;

	if ((gtid == GHOST_AGENT_GTID) && (run_flags != 0))
		return false;

	return true;
}

static inline bool commit_flags_valid(int commit_flags, int valid_commit_flags)
{
	if (commit_flags & ~valid_commit_flags)
		return false;

	/* Exactly one or none of the COMMIT_AT_XYZ flags must be set */
	BUILD_BUG_ON(sizeof_field(struct ghost_txn, commit_flags) != 1);
	if (hweight8(commit_flags & COMMIT_AT_FLAGS) > 1)
		return false;

	/* Cannot specify both elide barrier inc and inc on failure. */
	if ((commit_flags & ELIDE_AGENT_BARRIER_INC) &&
	    (commit_flags & INC_AGENT_BARRIER_ON_FAILURE))
		return false;

	return true;
}

/*
 * ghOSt API to yield local cpu or ping a remote cpu.
 *
 * Return 0 on success and -1 on failure.
 */
static int ghost_run(struct ghost_enclave *e, struct ghost_ioc_run __user *arg)
{
	struct task_struct *agent;
	struct rq_flags rf;
	struct rq *rq;
	int error = 0;
	int this_cpu;

	s64 gtid;
	u32 agent_barrier;
	u32 task_barrier;
	int run_cpu;
	int run_flags;
	struct ghost_ioc_run run_params;

	const int supported_flags = RTLA_ON_IDLE;

	if (!capable(CAP_SYS_NICE))
		return -EPERM;

	if (copy_from_user(&run_params, arg, sizeof(struct ghost_ioc_run)))
		return -EFAULT;

	gtid = run_params.gtid;
	agent_barrier = run_params.agent_barrier;
	task_barrier = run_params.task_barrier;
	run_cpu = run_params.run_cpu;
	run_flags = run_params.run_flags;

	if (run_cpu < 0 || run_cpu >= nr_cpu_ids || !cpu_online(run_cpu))
		return -EINVAL;

	if (!run_flags_valid(run_flags, supported_flags, gtid))
		return -EINVAL;

	preempt_disable();
	this_cpu = raw_smp_processor_id();

	switch (gtid) {
	case GHOST_NULL_GTID:	/* yield on local cpu */
		if (run_cpu != this_cpu)
			error = -EINVAL;
		break;
	case GHOST_AGENT_GTID:	/* ping agent */
		break;
	default:
		error = -EINVAL;
		break;
	}

	if (error)
		goto done;

	rq = cpu_rq(run_cpu);
	rq_lock_irq(rq, &rf);

	agent = rq->ghost.agent;
	if (unlikely(!agent)) {
		error = -EINVAL;
		rq_unlock_irq(rq, &rf);
		goto done;
	}

	/* ping agent */
	if (gtid == GHOST_AGENT_GTID) {
		if (same_process(agent, current)) {
			/* "serialize" with remote-agent doing a local run */
			agent_barrier_inc(rq);
			schedule_agent(rq, true);
		} else {
			error = -EINVAL;
		}
		rq_unlock_irq(rq, &rf);
		goto done;
	}

	/*
	 * Yield local cpu. Agent is voluntarily blocked in ghost_run() and
	 * returns when:
	 *
	 * - another agent "pings" it via ghost_run(AGENT_GTID).
	 * - a message is produced into a queue that the agent has expressed
	 *   an interest in (via ghost_wake_agent()).
	 * - a scheduling edge from an oncpu ghost task (e.g. blocked edge
	 *   or yield edge).
	 */
	VM_BUG_ON(gtid != GHOST_NULL_GTID);
	VM_BUG_ON(run_cpu != this_cpu);

	/*
	 * If an agent is going to block then we must be absolutely sure
	 * that its state is up-to-date (e.g. ping, remote-run or wakeup).
	 *
	 * The 'agent_barrier' check below guarantees this.
	 *
	 * The mb orders the blocked_in_run write before the barrier
	 * check in case of a concurrent wakeup.
	 */
	smp_store_mb(rq->ghost.blocked_in_run, true);
	if (unlikely(agent_barrier_get(agent) != agent_barrier)) {
		rq->ghost.blocked_in_run = false;
		rq_unlock_irq(rq, &rf);
		error = -ESTALE;
		goto done;
	}

	/*
	 * Reuse the latched task in case it was updated by a remote agent
	 * (before this local yield).
	 */
	ghost_set_pnt_state(rq, rq->ghost.latched_task, run_flags);

	rq_unlock_irq(rq, &rf);

	sched_preempt_enable_no_resched();

	schedule();

	/*
	 * Disable preemption to ensure that runqueue remains stable.
	 */
	preempt_disable();
	rq = this_rq();

	/*
	 * The agent is per-cpu and must always schedule on that CPU.
	 *
	 * In other words it cannot block or switch to 'next' on one
	 * CPU and wake up on a different one.
	 */
	VM_BUG_ON(rq->cpu != this_cpu);

	/*
	 * We reach this point after 'pick_next_task_ghost()' selected
	 * this agent to run and now we are returning back to userspace.
	 *
	 * 'blocked_in_run' must reflect that we are leaving ghost_run().
	 */
	VM_BUG_ON(rq->ghost.blocked_in_run);
done:
	preempt_enable_no_resched();

	return error;
}

static int __ghost_run_gtid_on(gtid_t gtid, u32 task_barrier, int run_flags,
			       int cpu, bool check_caller_enclave)
{
	struct rq_flags rf;
	struct rq *rq;
	int err = 0;
	struct task_struct *next;

	const int supported_flags = RTLA_ON_PREEMPT	|
				    RTLA_ON_BLOCKED	|
				    RTLA_ON_YIELD	|
				    NEED_L1D_FLUSH	|
				    ELIDE_PREEMPT	|
				    SEND_TASK_LATCHED	|
				    DO_NOT_PREEMPT	|
				    0;

	WARN_ON_ONCE(preemptible());

	if (cpu < 0)
		return -EINVAL;
	if (cpu >= nr_cpu_ids || !cpu_online(cpu))
		return -ERANGE;

	if (!run_flags_valid(run_flags, supported_flags, gtid))
		return -EINVAL;

	if (check_caller_enclave &&
	    !check_same_enclave(smp_processor_id(), cpu)) {
		return -EXDEV;
	}

	rcu_read_lock();
	next = find_task_by_gtid(gtid);
	if (next == NULL || next->ghost.agent) {
		rcu_read_unlock();
		return -ENOENT;
	}
	rq = task_rq_lock(next, &rf);
	rcu_read_unlock();

	err = validate_next_task(rq, next, task_barrier, /*state=*/ NULL);
	if (err) {
		task_rq_unlock(rq, next, &rf);
		return err;
	}

	if (task_running(rq, next)) {
		task_rq_unlock(rq, next, &rf);
		return -EBUSY;
	}

	rq = ghost_move_task(rq, next, cpu, &rf);

	/*
	 * Must not latch a task if there is no agent, otherwise PNT will never
	 * see it.  (Latched tasks are cleared when the agent exits).
	 */
	if (unlikely(!rq->ghost.agent)) {
		task_rq_unlock(rq, next, &rf);
		return -EINVAL;
	}

	if ((run_flags & DO_NOT_PREEMPT) &&
	    (task_has_ghost_policy(rq->curr) || rq->ghost.latched_task)) {
		task_rq_unlock(rq, next, &rf);
		return -ESTALE;
	}

	/*
	 * If the RQ is in the middle of PNT (where it briefly unlocks),
	 * ghost_can_schedule() is not accurate.  rq->curr is still the
	 * task that is scheduling, and it may be from CFS.
	 *
	 * This does not mean that our thread is in PNT.  It's possible that we
	 * are a wakeup BPF program and the PNT thread has unlocked the RQ and
	 * is running its own BPF program.  Either way, PNT will check for a
	 * latched task or for a higher priority task when it relocks.
	 */
	if (!rq->ghost.in_pnt_bpf && !ghost_can_schedule(rq, gtid)) {
		task_rq_unlock(rq, next, &rf);
		return -ENOSPC;
	}

	ghost_set_pnt_state(rq, next, run_flags);
	task_rq_unlock(rq, next, &rf);

	return 0;
}

static inline bool _ghost_txn_ready(int cpu, int *commit_flags)
{
	struct ghost_txn *txn;
	bool ready = false;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(cpu < 0 || cpu >= nr_cpu_ids);

	rcu_read_lock();
	txn = rcu_dereference(per_cpu(ghost_txn, cpu));
	if (txn) {
		ready = smp_load_acquire(&txn->state) == GHOST_TXN_READY;
		if (commit_flags != NULL)
			*commit_flags = READ_ONCE(txn->commit_flags);
	}
	rcu_read_unlock();

	return ready;
}

static inline bool ghost_txn_ready(int cpu)
{
	return _ghost_txn_ready(cpu, NULL);
}

static inline bool _ghost_txn_greedy(int commit_flags)
{
	return (commit_flags & COMMIT_AT_FLAGS) == 0;
}

static inline bool ghost_txn_greedy(int cpu)
{
	int flags;

	return _ghost_txn_ready(cpu, &flags) && _ghost_txn_greedy(flags);
}

/*
 * Try to claim txn iff the point-of-commit matches what was requested
 * via 'commit_flags'. Note that 'commit_flags == 0' indicates a greedy
 * commit and matches all commit points.
 *
 * The only exception is when a commit is explicitly requested by
 * the agent via GHOST_COMMIT_TXN in which case 'txn->commit_flags'
 * is ignored (indicated by where = -1).
 *
 * Returns 'true' if txn was claimed and 'false' otherwise.
 */
static inline bool ghost_claim_txn(int cpu, int where)
{
	struct ghost_txn *txn = rcu_dereference(per_cpu(ghost_txn, cpu));
	int commit_flags;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(cpu < 0 || cpu >= nr_cpu_ids);

	/*
	 * Ensure that COMMIT_AT_XYZ flag is never a negative value so
	 * that a commit explicitly requested by the agent can be safely
	 * indicated by where == -1.
	 */
	BUILD_BUG_ON(COMMIT_AT_FLAGS < 0);

	if (!txn || smp_load_acquire(&txn->state) != GHOST_TXN_READY)
		return false;

	commit_flags = READ_ONCE(txn->commit_flags);
	commit_flags &= COMMIT_AT_FLAGS;
	if (where >= 0 && commit_flags != 0 && commit_flags != where)
		return false;

	/*
	 * TODO: don't claim transaction if commit is going to fail
	 * (for e.g. if 'current' is in a higher priority sched_class).
	 *
	 * This behavior can be finessed using 'txn->flags'.
	 */
	return cmpxchg_acquire(&txn->state,
		    GHOST_TXN_READY, raw_smp_processor_id()) == GHOST_TXN_READY;
}

static inline bool txn_commit_allowed(struct rq *rq, gtid_t gtid, bool sync)
{
	/*
	 * Asynchronous commit is instigated by kernel and thus always
	 * allowed (e.g. return-to-user).
	 */
	if (!sync)
		return true;

	/* An agent is always allowed to commit synchronously. */
	if (current->ghost.agent)
		return true;

	/*
	 * A non-agent task is allowed to ping an agent as long as both
	 * belong to the same process.
	 */
	if (gtid == GHOST_AGENT_GTID && same_process(rq->ghost.agent, current))
		return true;

	return false;
}

/* Returns 'true' if txn commit is instigated by the agent on its own cpu */
static inline bool _local_commit(struct rq *rq, bool sync)
{
	int run_cpu = cpu_of(rq);
	int this_cpu = raw_smp_processor_id();

	lockdep_assert_held(&rq->lock);
	WARN_ON_ONCE(preemptible());

	return sync && this_cpu == run_cpu && is_agent(rq, current);
}

/* Returns 'true' if the agent is pinging itself */
static inline bool ping_self(struct rq *rq, bool sync, gtid_t gtid)
{
	return _local_commit(rq, sync) && gtid == GHOST_AGENT_GTID;
}

/*
 * Returns 'true' if agent is giving up the CPU because it is switching
 * to another ghost task or idling.
 */
static inline bool blocking_run(struct rq *rq, bool sync, gtid_t gtid)
{
	return _local_commit(rq, sync) && gtid != GHOST_AGENT_GTID;
}

static inline bool ghost_txn_succeeded(int state)
{
	return state == GHOST_TXN_COMPLETE;
}

/*
 * Caller is responsible for claiming txn (before calling this function)
 * and finalizing it (after this function returns).
 */
static bool _ghost_commit_txn(int run_cpu, bool sync, int64_t rendezvous,
			      int *commit_state, bool *need_rendezvous)
{
	gtid_t gtid;
	struct rq *rq = NULL;
	struct rq_flags rf;
	struct task_struct *next;
	bool local_run, resched = false;
	int commit_flags = 0, run_flags, state = GHOST_TXN_COMPLETE;
	struct ghost_txn *txn = rcu_dereference(per_cpu(ghost_txn, run_cpu));

	const int supported_run_flags = RTLA_ON_PREEMPT	|
					RTLA_ON_BLOCKED	|
					RTLA_ON_YIELD	|
					RTLA_ON_IDLE	|
					NEED_L1D_FLUSH	|
					ELIDE_PREEMPT	|
					NEED_CPU_NOT_IDLE |
					SEND_TASK_LATCHED |
					DEFER_LATCHED_PREEMPTION_BY_AGENT |
					DO_NOT_PREEMPT	|
					0;

	const int supported_commit_flags = COMMIT_AT_SCHEDULE		|
					   COMMIT_AT_TXN_COMMIT		|
					   ALLOW_TASK_ONCPU		|
					   ELIDE_AGENT_BARRIER_INC	|
					   INC_AGENT_BARRIER_ON_FAILURE	|
					   0;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(commit_state == NULL);
	VM_BUG_ON(need_rendezvous == NULL);
	VM_BUG_ON(run_cpu < 0 || run_cpu >= nr_cpu_ids);

	*need_rendezvous = false;

	if (!txn || txn->state != raw_smp_processor_id()) {
		state = GHOST_TXN_INVALID_CPU;
		goto out;
	}

	if (txn->version != GHOST_TXN_VERSION) {
		state = GHOST_TXN_UNSUPPORTED_VERSION;
		goto out;
	}

	if (txn->cpu != run_cpu) {
		state = GHOST_TXN_INVALID_CPU;
		goto out;
	}

	gtid = READ_ONCE(txn->gtid);
	run_flags = READ_ONCE(txn->run_flags);
	if (!run_flags_valid(run_flags, supported_run_flags, gtid)) {
		state = GHOST_TXN_INVALID_FLAGS;
		goto out;
	}

	commit_flags = READ_ONCE(txn->commit_flags);
	if (!commit_flags_valid(commit_flags, supported_commit_flags)) {
		state = GHOST_TXN_INVALID_FLAGS;
		goto out;
	}

	if (!cpu_online(run_cpu)) {
		state = GHOST_TXN_CPU_OFFLINE;
		goto out;
	}

	if (likely(gtid > 0)) {
		rcu_read_lock();
		next = find_task_by_gtid(gtid);
		if (next == NULL || next->ghost.agent) {
			rcu_read_unlock();
			state = next ? GHOST_TXN_INVALID_TARGET :
				       GHOST_TXN_TARGET_NOT_FOUND;
			goto out;
		}

		rq = task_rq_lock(next, &rf);
		rcu_read_unlock();

		if (validate_next_task(rq, next, txn->task_barrier, &state)) {
			task_rq_unlock(rq, next, &rf);
			rq = NULL;
			goto out;
		}

		if (!(commit_flags & ALLOW_TASK_ONCPU) ||
		    (task_cpu(next) != run_cpu)) {
			if (validate_next_offcpu(rq, next, &state)) {
				task_rq_unlock(rq, next, &rf);
				rq = NULL;
				goto out;
			}
		} else if (task_running(rq, next) &&
			   rq->ghost.must_resched &&
			   test_tsk_need_resched(next)) {
			/*
			 * 'next' is running but its oncpu days are numbered
			 * due to TIF_NEED_RESCHED. Specifically this handles
			 * the the race with ghost_wait_for_rendezvous() where
			 * it calls force_offcpu() due to an earlier poisoned
			 * rendezvous but hasn't scheduled yet (either hasn't
			 * reached a scheduling point or waiting for 'rq->lock'
			 * in __schedule).
			 *
			 * Fail the commit until 'next' gets fully offcpu.
			 */
			state = GHOST_TXN_TARGET_STALE;
			task_rq_unlock(rq, next, &rf);
			rq = NULL;
			goto out;
		}

		rq = ghost_move_task(rq, next, run_cpu, &rf);

		raw_spin_unlock(&next->pi_lock);    /* irqs still disabled */
	} else {
		if (gtid < GHOST_IDLE_GTID) {
			state = GHOST_TXN_INVALID_TARGET;
			goto out;
		}
		next = NULL;
		rq = cpu_rq(run_cpu);
		rq_lock_irqsave(rq, &rf);

		if (gtid == GHOST_IDLE_GTID)
			next = rq->idle;

		if (!(commit_flags & ALLOW_TASK_ONCPU)) {
			if (validate_next_offcpu(rq, next, &state))
				goto out;
		}
	}

	/*
	 * Update 'rq->ghost_rq' latch state for pick_next_task() to use
	 * when making a decision.
	 */
	if (unlikely(!rq->ghost.agent)) {
		state = GHOST_TXN_NO_AGENT;
		goto out;
	}

	if (unlikely(!rcu_dereference_sched(per_cpu(enclave, cpu_of(rq))))) {
		state = GHOST_TXN_CPU_UNAVAIL;
		goto out;
	}

	if (unlikely(!txn_commit_allowed(rq, gtid, sync))) {
		state = GHOST_TXN_NOT_PERMITTED;
		goto out;
	}

	if (next && (run_flags & DO_NOT_PREEMPT) &&
	    (task_has_ghost_policy(rq->curr) || rq->ghost.latched_task)) {
		state = GHOST_TXN_AGENT_STALE;
		goto out;
	}

	if (next && !ghost_can_schedule(rq, gtid)) {
		/*
		 * Transaction cannot be committed if CPU is not available
		 * (but only if 'next' is a task that can run elsewhere).
		 *
		 * Specifically if 'txn->gtid' is GHOST_AGENT_GTID there is
		 * no point returning an error because the agent cannot run
		 * anywhere else.
		 */
		state = GHOST_TXN_CPU_UNAVAIL;
		goto out;
	}

	local_run = blocking_run(rq, sync, gtid);
	if (local_run) {
		/*
		 * Agent is doing a synchronous commit on its local cpu and
		 * caller will schedule() on return. We ensure that its
		 * state is up-to-date via the 'agent_barrier' check below.
		 *
		 * The mb orders the blocked_in_run write before the barrier
		 * check in case of a concurrent wakeup.
		 */
		smp_store_mb(rq->ghost.blocked_in_run, true);
		if (agent_barrier_get(rq->ghost.agent) !=
		    READ_ONCE(txn->agent_barrier)) {
			rq->ghost.blocked_in_run = false;
			state = GHOST_TXN_AGENT_STALE;
			goto out;
		}
	} else {
		/*
		 * We do not assert a barrier match for the remote run case:
		 *
		 * In a remote run case we validate that that task_barrier
		 * is up-to-date (i.e. we have consumed the latest message for
		 * that task). We don't care so much about the agent_barrier
		 * because the agent is not blocking anyways.
		 *
		 * There is a danger in insisting that scheduling decisions be
		 * made on the most up-to-date state. In the limit this could
		 * lead to a livelock where the agent keeps making scheduling
		 * decisions (but never gets to act on it). Practically we need
		 * to consider the likelihood of a scheduling decision changing
		 * after consuming a pending message.
		 */
	}

	*need_rendezvous = true;
	resched = ghost_can_schedule(rq, gtid);

	if (next && task_running(rq, next)) {
		/* 'next' is already oncpu */
		VM_BUG_ON(!(commit_flags & ALLOW_TASK_ONCPU));
		resched = false;

		/*
		 * If 'next' is already oncpu and rendezvous is !poisoned
		 * then don't update rendezvous. Here's why:
		 * - if the sync_commit succeeds there is no benefit in
		 *   updating the rendezvous from one !poisoned value to
		 *   another !poisoned value (this is true even if 'next'
		 *   hasn't entered wait_for_rendezvous).
		 * - if the sync_commit fails (due to some other cpu) and
		 *   'next' hasn't entered wait_for_rendezvous yet then
		 *   updating rendezvous will force 'next' offcpu
		 *   (benign but unnecessary context switch).
		 *
		 * The basic idea is that if 'next' was able to get oncpu
		 * successfully then keep it there until it is explicitly
		 * preempted by the agent (yielding to CFS or bound to a
		 * different eg_core).
		 */
		WARN_ON_ONCE(!rendezvous_reached(rq->ghost.rendezvous));
		if (!rendezvous_poisoned(rq->ghost.rendezvous))
			*need_rendezvous = false;

		/*
		 * 'next' is already oncpu but a different task may be latched
		 * in 'latched_task' (for e.g. remote cpu has disabled irqs
		 * and a resched_ipi is pending). Alternately the remote cpu
		 * could be running the idle task organically and therefore
		 * 'rq->ghost.run_flags' needs to be updated.
		 *
		 * Set 'latched_task' to NULL to recreate the state right after
		 * 'next' got oncpu (see pick_next_task_ghost()).
		 */
		ghost_set_pnt_state(rq, NULL, run_flags);
	} else {
		/*
		 * 'next' may be NULL if 'txn->gtid' is one of the special
		 * encodings.
		 */

		/* "serialize" with remote-agent doing a local run */
		if (!(commit_flags & ELIDE_AGENT_BARRIER_INC))
			agent_barrier_inc(rq);

		/*
		 * Update latched task unless this is a ping in which case
		 * we'll get the agent running without clobbering an already
		 * latched task.
		 */
		if (likely(gtid != GHOST_AGENT_GTID))
			ghost_set_pnt_state(rq, next, run_flags);

		if (!next) {
			/* Handle special gtid encodings (e.g. ping) */
			schedule_next(rq, gtid, false);
		}
	}

	if (!local_run) {
		if (!sync) {
			VM_BUG_ON(run_cpu != raw_smp_processor_id());
			/*
			 * Agents have absolute priority over normal ghost
			 * tasks so no need to reschedule when the txn is
			 * asynchronously committed in agent context (e.g.
			 * return-to-user path).
			 */
			if (is_agent(rq, current))
				resched = false;
		} else {
			/* Don't schedule if agent is pinging its own CPU */
			if (ping_self(rq, sync, gtid))
				resched = false;
		}

		/*
		 * Elide the reschedule IPI if TIF_NEED_RESCHED is already set
		 * or if the target CPU is polling for it.
		 */
		if (resched) {
			resched = !test_tsk_need_resched(rq->curr) &&
				  set_nr_and_not_polling(rq->curr);
		}
	}
	VM_BUG_ON(local_run && !resched);  /* local_run must reschedule */

	/*
	 * Release store to ensure that TIF_NEED_RESCHED is visible on the
	 * remote cpu before GHOST_NO_RENDEZVOUS so we don't release an
	 * earlier sync-group transaction inadvertently.
	 */
	if (*need_rendezvous)
		smp_store_release(&rq->ghost.rendezvous, rendezvous);

	txn->cpu_seqnum = ++rq->ghost.cpu_seqnum;
out:
	if (rq) {
		lockdep_assert_held(&rq->lock);
		if (WARN_ON_ONCE(rq != cpu_rq(run_cpu))) {
			rq_unlock_irqrestore(rq, &rf);
			rq = NULL;
		}
	}

	if ((commit_flags & INC_AGENT_BARRIER_ON_FAILURE) &&
	    !ghost_txn_succeeded(state)) {
		if (!rq) {
			rq = cpu_rq(run_cpu);
			rq_lock_irqsave(rq, &rf);
		}
		agent_barrier_inc(rq);
	}

	if (rq)
		rq_unlock_irqrestore(rq, &rf);

	*commit_state = state;
	return resched;
}

static inline struct ghost_txn *_ghost_get_txn_ptr(int cpu)
{
	int this_cpu = raw_smp_processor_id();
	struct ghost_txn *txn = rcu_dereference(per_cpu(ghost_txn, cpu));

	VM_BUG_ON(preemptible());
	VM_BUG_ON(cpu < 0 || cpu >= nr_cpu_ids);
	if (txn && txn->state != this_cpu) {
		/* A buggy agent can trip this. */
		pr_info("txn->state for cpu %d was not %d!", txn->state,
			this_cpu);
	}

	return txn;
}

static inline void _ghost_set_txn_state(struct ghost_txn *txn,
					enum ghost_txn_state state)
{
	/*
	 * Set the time with a relaxed store since we update the txn state below
	 * with a release store. Userspace syncs with the kernel on that release
	 * store, so the release store acts a barrier.
	 */
	txn->commit_time = ktime_get_ns();
	smp_store_release(&txn->state, state);
}

static void ghost_set_txn_state(int cpu, enum ghost_txn_state state)
{
	struct ghost_txn *txn = _ghost_get_txn_ptr(cpu);

	if (txn)
		_ghost_set_txn_state(txn, state);
}

static inline void ghost_poison_txn(int cpu)
{
	ghost_set_txn_state(cpu, GHOST_TXN_POISONED);
}

static inline void ghost_claim_and_kill_txn(int cpu, enum ghost_txn_state err)
{
	/* claim_txn and set_txn_state must be called by the same cpu */
	preempt_disable();

	rcu_read_lock();
	if (unlikely(ghost_claim_txn(cpu, -1)))
		ghost_set_txn_state(cpu, err);
	rcu_read_unlock();

	/* We're often called from within the scheduler */
	preempt_enable_no_resched();
}

static bool ghost_commit_txn(int run_cpu, bool sync, int *commit_state)
{
	int state;
	bool resched, need_rendezvous;

	resched = _ghost_commit_txn(run_cpu, sync, GHOST_NO_RENDEZVOUS, &state,
				    &need_rendezvous);
	if (commit_state)
		*commit_state = state;

	ghost_set_txn_state(run_cpu, state);
	return resched;
}

#if defined(CONFIG_X86_64) || defined(CONFIG_X86)
static inline void ghost_send_reschedule(struct cpumask *mask)
{
	int cpu;

	for_each_cpu(cpu, mask) {
		if (try_ipiless_wakeup(cpu))
			__cpumask_clear_cpu(cpu, mask);
	}

	if (!cpumask_empty(mask))
		apic->send_IPI_mask(mask, RESCHEDULE_VECTOR);

#ifdef CONFIG_DEBUG_GHOST
	/*
	 * 'mask' can be modified non-deterministically due to ipiless wakeup
	 * above and callers must not assume that 'mask' is same before and
	 * after the call.
	 *
	 * Weed out such callers by clobbering 'mask' in debug builds.
	 */
	cpumask_clear(mask);
#endif
}
#else
static inline void ghost_send_reschedule(struct cpumask *mask)
{
	int cpu;

	for_each_cpu(cpu, mask)
		smp_send_reschedule(cpu);
}
#endif

static void _ghost_commit_pending_txn(int cpu, int where)
{
	if (unlikely(ghost_claim_txn(cpu, where)))
		ghost_commit_txn(cpu, false, NULL);
}

static void ghost_commit_pending_txn(int where)
{
	int cpu = get_cpu();

	rcu_read_lock();
	_ghost_commit_pending_txn(cpu, where);
	rcu_read_unlock();

	put_cpu();
}

static void _commit_greedy_txn(int cpu)
{
	WARN_ON_ONCE(preemptible());

	rcu_read_lock();
	_ghost_commit_pending_txn(cpu, /*where=*/0);
	rcu_read_unlock();
}

void ghost_commit_all_greedy_txns(void)
{
	int cpu, this_cpu;
	struct ghost_enclave *e;
	cpumask_var_t ipimask;

	/*
	 * 'cpumask_var_t' currently allocates CPU masks on the stack since
	 * CONFIG_CPUMASK_OFFSTACK is not set. If this flag does become set in
	 * the future, 'cpumask_var_t' becomes a pointer and
	 * 'zalloc_cpumask_var' allocates memory rather than act as a no-op. In
	 * that case, we will likely want to preallocate 'ipimask' for each CPU
	 * when the transaction region is set up rather than allocate memory on
	 * every timer tick. This warning will get our attention if the flag is
	 * set.
	 */
#ifdef CONFIG_CPUMASK_OFFSTACK
	WARN_ONCE(1, "Pre-allocate cpumasks");
#endif

	if (!zalloc_cpumask_var(&ipimask, GFP_ATOMIC))
		return;

	this_cpu = get_cpu();
	rcu_read_lock();
	e = rcu_dereference(per_cpu(enclave, this_cpu));
	if (!e)
		goto done;
	/*
	 * Note that e's cpu mask could be changed concurrently, with cpus added
	 * or removed.  This is benign.  First, any commits will look at the
	 * rcu-protected ghost_txn pointer.  That's what really matters, and
	 * any caller to __enclave_remove_cpu() will synchronize_rcu().
	 *
	 * Furthermore, if a cpu is added while we are looking (which is not
	 * protected by RCU), it's not a big deal.  This is a greedy commit, and
	 * we'll catch it on the next tick.
	 */
	for_each_cpu(cpu, &e->cpus) {
		/*
		 * Send a resched IPI to remote CPUs (and do not commit those
		 * txns) but commit a txn for this CPU.
		 */
		if (cpu == this_cpu)
			ghost_commit_greedy_txn();
		else if (ghost_txn_greedy(cpu))
			__cpumask_set_cpu(cpu, ipimask);
	}
	/* Poke the remote CPUs so that they see their pending txns. */
	ghost_send_reschedule(ipimask);
done:
	free_cpumask_var(ipimask);
	rcu_read_unlock();
	put_cpu();
}

static void ghost_reached_rendezvous(int cpu, int64_t target)
{
	struct rq *rq;

	WARN_ON_ONCE(preemptible());

	rq = cpu_rq(cpu);
	smp_store_release(&rq->ghost.rendezvous, target);
}

static int ghost_sync_group(struct ghost_enclave *e,
			    struct ghost_ioc_commit_txn __user *arg)
{
	int64_t target;
	bool failed = false;
	bool local_resched = false;
	int cpu, this_cpu, error, state;
	cpumask_var_t cpumask, ipimask, rendmask;

	ulong *user_mask_ptr;
	uint user_mask_len;
	int flags;
	struct ghost_ioc_commit_txn commit_txn;

	const int valid_flags = 0;

	if (copy_from_user(&commit_txn, arg,
			   sizeof(struct ghost_ioc_commit_txn)))
		return -EFAULT;

	user_mask_ptr = commit_txn.mask_ptr;
	user_mask_len = commit_txn.mask_len;
	flags = commit_txn.flags;

	if (flags & ~valid_flags)
		return -EINVAL;

	if (!alloc_cpumask_var(&cpumask, GFP_KERNEL))
		return -ENOMEM;

	error = get_user_cpu_mask(user_mask_ptr, user_mask_len, cpumask);
	if (error) {
		free_cpumask_var(cpumask);
		return error;
	}

	if (!zalloc_cpumask_var(&ipimask, GFP_KERNEL)) {
		free_cpumask_var(cpumask);
		return -ENOMEM;
	}

	if (!zalloc_cpumask_var(&rendmask, GFP_KERNEL)) {
		free_cpumask_var(cpumask);
		free_cpumask_var(ipimask);
		return -ENOMEM;
	}

	preempt_disable();
	this_cpu = raw_smp_processor_id();
	target = ghost_sync_group_cookie();

	rcu_read_lock();

	/*
	 * Claim all transactions. We have the following invariant at the
	 * end of the loop:
	 * 'failed'	'cpumask'
	 * false	all sync_group cpus.
	 * true		subset of sync_group cpus with claimed txns.
	 */
	for_each_cpu(cpu, cpumask) {
		if (!ghost_claim_txn(cpu, -1)) {
			/*
			 * This is not expected and points at a programming
			 * error in the agent (e.g. txn was async committed
			 * on another cpu).
			 */
			failed = true;
			__cpumask_clear_cpu(cpu, cpumask);
		}
	}

	/*
	 * Commit transactions. We have the following invariant at the end
	 * of the loop:
	 * 'failed'	'cpumask'
	 * false	all sync_group cpus.
	 * true		sync_group subset with successfully committed txns.
	 *
	 * In either case 'ipimask' contains the CPUs that must be interrupted
	 * to observe the updated scheduling state. It is always a a subset of
	 * 'cpumask' because:
	 * - TIF_NEED_RESCHED already set or remote cpu is polling for it.
	 * - reschedule on the local cpu is captured in 'local_resched'.
	 *
	 * Note that for_each_cpu_wrap() guarantees that 'this_cpu' is the
	 * last cpu visited in the loop. This lets _ghost_commit_txn() set
	 * 'blocked_in_run=true' for local commits safely (otherwise the
	 * caller needs to clear 'blocked_in_run' if the overall sync_group
	 * fails to commit subsequently).
	 */
	for_each_cpu_wrap(cpu, cpumask, this_cpu + 1) {
		bool resched, need_rendezvous;
		struct rq *rq = cpu_rq(cpu);
		struct rq_flags rf;
		struct ghost_txn *txn;
		int commit_flags;

		/*
		 * No point in committing this txn if we know a prior txn
		 * failed to commit.
		 */
		if (failed) {
			txn = rcu_dereference(per_cpu(ghost_txn, cpu));
			commit_flags = READ_ONCE(txn->commit_flags);

			if (commit_flags & INC_AGENT_BARRIER_ON_FAILURE) {
				rq_lock_irqsave(rq, &rf);
				agent_barrier_inc(rq);
				rq_unlock_irqrestore(rq, &rf);
			}
			ghost_poison_txn(cpu);
			__cpumask_clear_cpu(cpu, cpumask);
			continue;
		}

		resched = _ghost_commit_txn(cpu, true, -target, &state,
					    &need_rendezvous);
		if (!ghost_txn_succeeded(state)) {
			VM_BUG_ON(resched);
			VM_BUG_ON(need_rendezvous);
			failed = true;
			ghost_set_txn_state(cpu, state);
			__cpumask_clear_cpu(cpu, cpumask);
		} else {
			if (resched) {
				VM_BUG_ON(!need_rendezvous);
				if (cpu == this_cpu)
					local_resched = true;
				else
					__cpumask_set_cpu(cpu, ipimask);
			}

			if (need_rendezvous)
				__cpumask_set_cpu(cpu, rendmask);
		}
	}

	/*
	 * Send resched IPI to CPUs that traverse the need_resched edge (0->1).
	 *
	 * _ghost_commit_txn() assumes that if need_resched is set then an IPI
	 * must have been already sent.
	 */
	ghost_send_reschedule(ipimask);

	/*
	 * The overall sync_group failed but we may have successfully updated
	 * scheduling state on a subset of CPUs. Poison 'target' to get these
	 * cpus to reschedule immediately after reaching rendezvous.
	 */
	if (failed)
		target |= GHOST_POISONED_RENDEZVOUS;

	for_each_cpu(cpu, rendmask)
		ghost_reached_rendezvous(cpu, target);

	state = failed ? GHOST_TXN_POISONED : GHOST_TXN_COMPLETE;
	for_each_cpu(cpu, cpumask) {
		struct ghost_txn *txn = _ghost_get_txn_ptr(cpu);

		if (!txn) {
			/*
			 * We've committed, but the cpu has since been removed
			 * from the enclave.  Possibly it's destroyed.
			 */
			continue;
		}
		_ghost_set_txn_state(txn, state);
		if (!failed) {
			/*
			 * Release ownership in case we end up scheduling on
			 * this cpu (thus precluding the agent from doing so
			 * itself). When control eventually returns to the
			 * agent the return value can be used to detect a
			 * successful commit.
			 *
			 * N.B. even though not strictly necessary the txn
			 * ownership is released even if the local cpu is
			 * not scheduling. This is intentional to keep the
			 * userspace code consistent (it doesn't need to
			 * distinguish between local/remote sync commits).
			 */
			smp_store_release(&txn->u.sync_group_owner, -1);
		} else {
			/*
			 * The commit failed but the agent retains ownership
			 * of the transactions in the sync_group. The agent
			 * can release ownership after it has inspected the
			 * reason for failure.
			 */
		}
	}

	rcu_read_unlock();

	/* Reschedule (potentially switching to 'latched_task'). */
	if (local_resched) {
		WARN_ON_ONCE(failed);
		ghost_agent_schedule();
	}

	WARN_ON_ONCE(this_rq()->ghost.blocked_in_run);

	preempt_enable_no_resched();
	free_cpumask_var(cpumask);
	free_cpumask_var(ipimask);
	free_cpumask_var(rendmask);
	return !failed;
}

static int ioctl_ghost_commit_txn(struct ghost_enclave *e,
				  struct ghost_ioc_commit_txn __user *arg)
{
	int error, state;
	int cpu, this_cpu;
	int failed_commits = 0;
	bool local_resched = false;
	cpumask_var_t cpumask, ipimask;

	ulong *user_mask_ptr;
	uint user_mask_len;
	int flags;
	struct ghost_ioc_commit_txn commit_txn;

	const int valid_flags = 0;

	if (copy_from_user(&commit_txn, arg,
			   sizeof(struct ghost_ioc_commit_txn)))
		return -EFAULT;

	user_mask_ptr = commit_txn.mask_ptr;
	user_mask_len = commit_txn.mask_len;
	flags = commit_txn.flags;

	if (flags & ~valid_flags)
		return -EINVAL;

	if (!alloc_cpumask_var(&cpumask, GFP_KERNEL))
		return -ENOMEM;

	error = get_user_cpu_mask(user_mask_ptr, user_mask_len, cpumask);
	if (error) {
		free_cpumask_var(cpumask);
		return error;
	}

	if (!zalloc_cpumask_var(&ipimask, GFP_KERNEL)) {
		free_cpumask_var(cpumask);
		return -ENOMEM;
	}

#ifdef notyet
	/* Restrict 'cpumask' to the current enclave. */
	ghost_enclave_cpus_allowed(current, cpus_allowed);
	cpumask_and(cpumask, cpumask, cpus_allowed);
#endif

	preempt_disable();
	this_cpu = raw_smp_processor_id();

	rcu_read_lock();
	for_each_cpu_wrap(cpu, cpumask, this_cpu + 1) {
		int commit_flags;
		bool greedy_commit, inline_commit;

		if (!_ghost_txn_ready(cpu, &commit_flags))
			continue;

		greedy_commit = _ghost_txn_greedy(commit_flags);
		inline_commit = (commit_flags & COMMIT_AT_TXN_COMMIT);

		if (cpu != this_cpu && !inline_commit) {
			/*
			 * Only send an IPI if transaction can be committed by
			 * the remote CPU. Notably this excludes transactions
			 * that must be committed in specific code paths (for
			 * e.g. COMMIT_AT_SCHEDULE used for a pre-staged txn).
			 */
			if (greedy_commit)
				__cpumask_set_cpu(cpu, ipimask);

			continue;
		}

		/*
		 * Agent wants us to commit a transaction whose 'commit_flags'
		 * indicate that it should be committed elsewhere (for e.g.
		 * COMMIT_AT_SCHEDULE for a pre-staged transaction).
		 */
		WARN_ONCE(!greedy_commit && !inline_commit,
			  "Unexpected txn->commit_flags %#x on cpu %d",
			  commit_flags, cpu);

		/*
		 * Commit txn locally either because it targets 'this_cpu'
		 * or caller wants it committed inline.
		 */
		if (!ghost_claim_txn(cpu, -1)) {
			failed_commits++;
			continue;
		}

		/*
		 * If there are failed commits then poison the local commit
		 * so we'll return from this syscall immediately (as opposed
		 * to switching to a task which would delay reaction to the
		 * failed commits).
		 *
		 * Note that for_each_cpu_wrap() guarantees that 'this_cpu'
		 * is the last cpu visited in the loop so 'failed_commits'
		 * is final.
		 */
		if (failed_commits > 0 && cpu == this_cpu) {
			ghost_poison_txn(cpu);
			continue;
		}

		if (ghost_commit_txn(cpu, true, &state)) {
			WARN_ON_ONCE(!ghost_txn_succeeded(state));
			if (cpu == this_cpu)
				local_resched = true;
			else
				__cpumask_set_cpu(cpu, ipimask);
		} else if (!ghost_txn_succeeded(state)) {
			failed_commits++;
		} else {
			/* commit succeeded, resched not needed */
		}
	}
	rcu_read_unlock();

	ghost_send_reschedule(ipimask);

	/* Reschedule (potentially switching to 'latched_task'). */
	if (local_resched) {
		WARN_ON_ONCE(failed_commits);
		ghost_agent_schedule();
	}

	WARN_ON_ONCE(this_rq()->ghost.blocked_in_run);

	preempt_enable_no_resched();
	free_cpumask_var(cpumask);
	free_cpumask_var(ipimask);
	return 0;
}

static int ghost_timerfd_validate(struct timerfd_ghost *timerfd_ghost)
{
	int cpu;
	struct rq *rq;
	struct rq_flags rf;
	const int valid_flags = TIMERFD_GHOST_ENABLED;

	if (timerfd_ghost->flags & ~valid_flags)
		return -EINVAL;

	/* ghost interaction disabled for this timerfd */
	if (!(timerfd_ghost->flags & TIMERFD_GHOST_ENABLED))
		return 0;

	cpu = timerfd_ghost->cpu;
	if (cpu < 0 || cpu >= nr_cpu_ids || !cpu_online(cpu))
		return -EINVAL;

	rq = cpu_rq(cpu);
	rq_lock_irqsave(rq, &rf);

	if (!rq->ghost.agent || !same_process(rq->ghost.agent, current)) {
		rq_unlock_irqrestore(rq, &rf);
		return -EINVAL;
	}

	rq_unlock_irqrestore(rq, &rf);
	return 0;
}

/* fs/timerfd.c */
int do_timerfd_settime(int ufd, int flags, const struct itimerspec64 *new,
		       struct itimerspec64 *old,
		       struct __kernel_timerfd_ghost *ktfd);

static int ghost_timerfd_settime(struct ghost_ioc_timerfd_settime __user *arg)
{
	struct itimerspec64 new, old;
	int ret;

	int timerfd, flags;
	const struct __kernel_itimerspec *itmr;
	struct __kernel_itimerspec *otmr;
	struct timerfd_ghost timerfd_ghost;
	struct ghost_ioc_timerfd_settime settime_data;
	struct __kernel_timerfd_ghost ktfd_ghost;

	if (copy_from_user(&settime_data, arg,
			   sizeof(struct ghost_ioc_timerfd_settime)))
		return -EFAULT;

	timerfd = settime_data.timerfd;
	flags = settime_data.flags;
	itmr = settime_data.in_tmr;
	otmr = settime_data.out_tmr;
	timerfd_ghost = settime_data.timerfd_ghost;

	if (get_itimerspec64(&new, itmr))
		return -EFAULT;

	ret = ghost_timerfd_validate(&timerfd_ghost);
	if (ret)
		return ret;

	ktfd_ghost.enabled = timerfd_ghost.flags & TIMERFD_GHOST_ENABLED;
	ktfd_ghost.cpu = timerfd_ghost.cpu;
	ktfd_ghost.type = timerfd_ghost.type;
	ktfd_ghost.cookie = timerfd_ghost.cookie;

	ret = do_timerfd_settime(timerfd, flags, &new, &old, &ktfd_ghost);
	if (ret)
		return ret;

	if (otmr && put_itimerspec64(&old, otmr))
		return -EFAULT;

	return ret;
}

static void _ghost_timerfd_triggered(int cpu, uint64_t type, uint64_t cookie)
{
	struct rq *rq;
	struct rq_flags rf;

	if (WARN_ON_ONCE(cpu < 0 || cpu >= nr_cpu_ids || !cpu_online(cpu)))
		return;

	rq = cpu_rq(cpu);
	rq_lock_irqsave(rq, &rf);

	if (cpu_deliver_timer_expired(rq, type, cookie))
		ghost_wake_agent_on(agent_target_cpu(rq));

	rq_unlock_irqrestore(rq, &rf);
}

#ifndef SYS_SWITCHTO_SWITCH_FLAGS_LAZY_EXEC_CLOCK
#define SYS_SWITCHTO_SWITCH_FLAGS_LAZY_EXEC_CLOCK	0x10000
#endif

static void _ghost_switchto(struct rq *rq, struct task_struct *prev,
			    struct task_struct *next, int switchto_flags)
{
	VM_BUG_ON(rq->ghost.check_prev_preemption);
	VM_BUG_ON(rq->ghost.switchto_count < 0);

	if (switchto_flags & SYS_SWITCHTO_SWITCH_FLAGS_LAZY_EXEC_CLOCK) {
		next->se.exec_start = prev->se.exec_start;
	} else {
		_update_curr_ghost(rq);
		next->se.exec_start = rq_clock_task(rq);
	}

	list_del_init(&prev->ghost.run_list);
	ghost_sw_clear_flag(prev->ghost.status_word, GHOST_SW_TASK_RUNNABLE);

	list_add_tail(&next->ghost.run_list, &rq->ghost.tasks);
	next->ghost.last_runnable_at = 0;	/* we're on_cpu */
	ghost_sw_set_time(next->ghost.status_word, ktime_get_ns());
	ghost_sw_set_flag(next->ghost.status_word,
			  GHOST_SW_TASK_RUNNABLE | GHOST_SW_TASK_ONCPU);

	if (++rq->ghost.switchto_count == 1) {
		/*
		 * Produce MSG_TASK_SWITCHTO but don't wake up the agent.
		 * In per-cpu models, agent wakeup will preempt the task
		 * and break the switchto chain before it even gets started.
		 */
		task_deliver_msg_switchto(rq, prev);
	}
}

static void ghost_need_cpu_not_idle(struct rq *rq, struct task_struct *next)
{
	if (cpu_deliver_msg_not_idle(rq, next))
		ghost_wake_agent_on(agent_target_cpu(rq));
}

static void cpu_idle(struct rq *rq)
{
	struct rq_flags rf;

	rq_lock_irq(rq, &rf);
	if (rq->ghost.dont_idle_once) {
		set_tsk_need_resched(current);
		set_preempt_need_resched();
		rq->ghost.dont_idle_once = false;
	}
	rq_unlock_irq(rq, &rf);
}

/* Helper for when you "echo foo > ctl" without the -n. */
static void strip_slash_n(char *buf, size_t count)
{
	char *n = strnchr(buf, count, '\n');

	if (n)
		*n = '\0';
}

struct gf_dirent {
	char			*name;
	umode_t			mode;
	struct kernfs_ops	*ops;
	loff_t			size;
	bool			is_dir;
};

/*
 * Finds a specific file in a directory table.  This is useful for runtime
 * initialization, though keep in mind the dirtab is a global structure.
 */
static struct gf_dirent *gf_find_file(struct gf_dirent *dirtab,
				      const char *name)
{
	struct gf_dirent *gft;

	for (gft = dirtab; gft->name; gft++) {
		if (!strcmp(gft->name, name))
			return gft;
	}
	return NULL;
}

/*
 * Every open file in an enclave holds a kref on the enclave.  This includes the
 * ctl, txn, the status words, etc.
 *
 * Each of those file's priv points to the enclave struct, either directly or
 * indirectly.  For instance, the SW files have their own object that points to
 * the enclave.  We can differentiate which file is which based on the kernfs
 * ops.  In some cases, we can reuse ops and differentiate on the object's name.
 *
 * This does not include the enclave directory; it's priv is NULL, and it has no
 * function ops.
 *
 * Destroying the enclave involves removing it from the filesystem by writing
 * "destroy" into ctl.  That triggers kernfs_remove() and whatever things we
 * want to do for the enclave itself, like killing the agents.  The enclave
 * object will exist until the last FD is closed.  Note that when we call
 * kernfs_remove(), it'll "drain" any open files, which involves unmapping any
 * mmapped files.
 *
 * Most of the heavy lifting for destroying an enclave is done in
 * ghost_destroy_enclave().  The kernel scheduler may call that function at any
 * moment if it determines an enclave misbehaved.
 */

static struct ghost_enclave *of_to_e(struct kernfs_open_file *of)
{
	return of->kn->priv;
}

static struct ghost_enclave *seq_to_e(struct seq_file *sf)
{
	struct kernfs_open_file *of = sf->private;

	return of_to_e(of);
}

/* For enclave files whose priv directly points to a ghost enclave. */
static int gf_e_open(struct kernfs_open_file *of)
{
	struct ghost_enclave *e = of_to_e(of);

	/*
	 * kernfs open can grab kernfs_mutex, which is a potential deadlock
	 * scenario.  agent's should open files from CFS.
	 */
	if (!READ_ONCE(e->live_dangerously))
		WARN_ON_ONCE(is_agent(task_rq(current), current));

	kref_get(&e->kref);
	return 0;
}

/* For enclave files whose priv directly points to a ghost enclave. */
static void gf_e_release(struct kernfs_open_file *of)
{
	struct ghost_enclave *e = of_to_e(of);

	kref_put(&e->kref, enclave_release);
}

static int gf_abi_version_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	WARN_ON_ONCE(e->abi->version != GHOST_VERSION);
	seq_printf(sf, "%u\n", e->abi->version);
	return 0;
}

static struct kernfs_ops gf_ops_e_abi_version = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_abi_version_show,
};

/*
 * There can be at most one writable open, and there can be any number of
 * read-only opens.
 *
 * If there is a writable open, that means userspace has advertised this enclave
 * as having an agent_online, and the value of agent_online will change
 * accordingly.
 */
static int gf_agent_online_open(struct kernfs_open_file *of)
{
	struct ghost_enclave *e = of_to_e(of);
	unsigned long irq_fl;

	if (!(of->file->f_mode & FMODE_WRITE))
		goto done;

	spin_lock_irqsave(&e->lock, irq_fl);
	if (e->agent_online) {
		spin_unlock_irqrestore(&e->lock, irq_fl);
		return -EBUSY;
	}
	e->agent_online = true;
	spin_unlock_irqrestore(&e->lock, irq_fl);

	kernfs_notify(of->kn);

done:
	kref_get(&e->kref);
	return 0;
}

static void gf_agent_online_release(struct kernfs_open_file *of)
{
	struct ghost_enclave *e = of_to_e(of);
	unsigned long irq_fl;

	if (!(of->file->f_mode & FMODE_WRITE))
		goto done;

	spin_lock_irqsave(&e->lock, irq_fl);
	WARN_ONCE(!e->agent_online,
		  "closing RW agent_online for enclave_%lu, but it's not online!",
		  e->id);
	e->agent_online = false;
	spin_unlock_irqrestore(&e->lock, irq_fl);

	/*
	 * Kicks any epoll/notifiers about the change in state.  This is the
	 * "agent death edge".
	 *
	 * Note that this doesn't necessarily mean the enclave will be
	 * destroyed, merely that userspace no longer thinks there is a valid
	 * agent.  This FD was probably closed because the agent crashed.
	 */
	kernfs_notify(of->kn);

done:
	kref_put(&e->kref, enclave_release);
}

static int gf_agent_online_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%u", e->agent_online ? 1 : 0);
	return 0;
}

static ssize_t gf_agent_online_write(struct kernfs_open_file *of, char *buf,
				     size_t bytes, loff_t off)
{
	/* We need a write op so kernfs allows us to be opened for writing. */
	return -EINVAL;
}

static struct kernfs_ops gf_ops_e_agent_online = {
	.open			= gf_agent_online_open,
	.release		= gf_agent_online_release,
	.seq_show		= gf_agent_online_show,
	.write			= gf_agent_online_write,
};

static int gf_commit_at_tick_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%d", READ_ONCE(e->commit_at_tick));
	return 0;
}

static ssize_t gf_commit_at_tick_write(struct kernfs_open_file *of, char *buf,
				       size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	int tunable;

	err = kstrtoint(buf, 0, &tunable);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->commit_at_tick, !!tunable);

	return len;
}

static struct kernfs_ops gf_ops_e_commit_at_tick = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_commit_at_tick_show,
	.write			= gf_commit_at_tick_write,
};

static int gf_cpu_data_mmap(struct kernfs_open_file *of,
			       struct vm_area_struct *vma)
{
	struct ghost_enclave *e = of_to_e(of);

	return ghost_cpu_data_mmap(of->file, vma, e->cpu_data,
				   of->kn->attr.size);
}

static struct kernfs_ops gf_ops_e_cpu_data = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.mmap			= gf_cpu_data_mmap,
};

/* Returns an ASCII list of the cpus in the enclave */
static ssize_t gf_cpulist_read(struct kernfs_open_file *of, char *buf,
			       size_t bytes, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	unsigned long fl;
	cpumask_var_t cpus;
	char *pagebuf;
	ssize_t strlen;

	if (off > PAGE_SIZE)
		return -EINVAL;
	bytes = min_t(size_t, bytes, PAGE_SIZE - off);

	if (!alloc_cpumask_var(&cpus, GFP_KERNEL))
		return -ENOMEM;

	spin_lock_irqsave(&e->lock, fl);
	memcpy(cpus, &e->cpus, cpumask_size());
	spin_unlock_irqrestore(&e->lock, fl);

	pagebuf = (char *)get_zeroed_page(GFP_KERNEL);
	if (!pagebuf) {
		free_cpumask_var(cpus);
		return -ENOMEM;
	}

	strlen = cpumap_print_to_pagebuf(/*list=*/true, pagebuf, cpus);
	bytes = memory_read_from_buffer(buf, bytes, &off, pagebuf, strlen);

	free_page((unsigned long)pagebuf);
	free_cpumask_var(cpus);

	return bytes;
}


static ssize_t __cpu_set_write(struct kernfs_open_file *of, char *buf,
			       size_t bytes, loff_t off, bool is_list)
{
	cpumask_var_t cpus;
	int err;

	if (!alloc_cpumask_var(&cpus, GFP_KERNEL))
		return -ENOMEM;
	if (is_list)
		err = cpulist_parse(buf, cpus);
	else
		err = cpumask_parse(buf, cpus);
	if (err) {
		free_cpumask_var(cpus);
		return err;
	}
	err = ghost_enclave_set_cpus(of_to_e(of), cpus);
	free_cpumask_var(cpus);
	return err ? err : bytes;
}

/* Sets the enclave's cpus to buf, an ASCII list of cpus. */
static ssize_t gf_cpulist_write(struct kernfs_open_file *of, char *buf,
				size_t bytes, loff_t off)
{
	return __cpu_set_write(of, buf, bytes, off, /*is_list=*/true);
}

static struct kernfs_ops gf_ops_e_cpulist = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.read			= gf_cpulist_read,
	.write			= gf_cpulist_write,
};

/* Returns an ASCII hex mask of the cpus in the enclave */
static ssize_t gf_cpumask_read(struct kernfs_open_file *of, char *buf,
			       size_t bytes, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	unsigned long fl;
	cpumask_var_t cpus;
	char *mask_str;
	int len;

	if (!alloc_cpumask_var(&cpus, GFP_KERNEL))
		return -ENOMEM;

	spin_lock_irqsave(&e->lock, fl);
	memcpy(cpus, &e->cpus, cpumask_size());
	spin_unlock_irqrestore(&e->lock, fl);

	/*
	 * +1 for the \0.  We won't return the \0 to userspace, but the string
	 * will be null-terminated while in the kernel.
	 */
	len = snprintf(NULL, 0, "%*pb\n", cpumask_pr_args(cpus)) + 1;
	mask_str = kmalloc(len, GFP_KERNEL);
	if (!mask_str) {
		free_cpumask_var(cpus);
		return -ENOMEM;
	}
	len = snprintf(mask_str, len, "%*pb\n", cpumask_pr_args(cpus));
	bytes = memory_read_from_buffer(buf, bytes, &off, mask_str, len);

	kfree(mask_str);
	free_cpumask_var(cpus);

	return bytes;
}

/* Sets the enclave's cpus to buf, an ASCII hex cpumask. */
static ssize_t gf_cpumask_write(struct kernfs_open_file *of, char *buf,
				size_t bytes, loff_t off)
{
	return __cpu_set_write(of, buf, bytes, off, /*is_list=*/false);
}

static struct kernfs_ops gf_ops_e_cpumask = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.read			= gf_cpumask_read,
	.write			= gf_cpumask_write,
};

static int gf_ctl_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%lu", e->id);
	return 0;
}

static void destroy_enclave(struct kernfs_open_file *ctl_of)
{
	struct kernfs_node *ctl = ctl_of->kn;
	struct ghost_enclave *e = of_to_e(ctl_of);

	/*
	 * kernfs_remove() works recursively, removing the entire enclave
	 * directory.  We need to remove the ctl file first, since we're in the
	 * middle of a kn op.
	 *
	 * Multiple threads can call kernfs_remove_self() at once.  Whichever
	 * succeeds will remove the directory and release e.
	 */
	if (!kernfs_remove_self(ctl))
		return;
	if (WARN_ON(ctl->parent != e->enclave_dir))
		return;
	ghost_destroy_enclave(e);
}

static int ctl_become_agent(struct kernfs_open_file *of, int qfd)
{
	struct ghost_enclave *e = of_to_e(of);
	struct ghost_enclave *old_target;
	int ret;
	struct sched_param param = {
		.sched_priority = qfd,
	};

	/*
	 * See _ghost_setscheduler() for the meaning of sched_priority.
	 * -1 is valid.  It means "give me the default queue".
	 */
	if (qfd < -1)
		return -EBADF;

	old_target = set_target_enclave(e);
	ret = sched_setscheduler(current, SCHED_GHOST | SCHED_RESET_ON_FORK,
				 &param);
	restore_target_enclave(old_target);
	return ret;
}

static struct ghost_sw_region *of_to_swr(struct kernfs_open_file *of)
{
	return of->kn->priv;
}

/*
 * swr_kns refcount the enclave, even though they point to the swr.  An swr will
 * never be deleted until the enclave is released.
 */
static int gf_swr_open(struct kernfs_open_file *of)
{
	struct ghost_sw_region *swr = of_to_swr(of);

	/*
	 * kernfs open can grab kernfs_mutex, which is a potential deadlock
	 * scenario.  agent's should open files from CFS.
	 */
	WARN_ON_ONCE(is_agent(task_rq(current), current));

	kref_get(&swr->enclave->kref);
	return 0;
}

static void gf_swr_release(struct kernfs_open_file *of)
{
	struct ghost_sw_region *swr = of_to_swr(of);

	kref_put(&swr->enclave->kref, enclave_release);
}

static int gf_swr_mmap(struct kernfs_open_file *of, struct vm_area_struct *vma)
{
	struct ghost_sw_region *swr = of_to_swr(of);

	if (vma->vm_flags & VM_WRITE)
		return -EINVAL;
	vma->vm_flags &= ~VM_MAYWRITE;

	return ghost_region_mmap(of->file, vma, swr->header, of->kn->attr.size);
}

static struct kernfs_ops gf_ops_e_swr = {
	.open			= gf_swr_open,
	.release		= gf_swr_release,
	.mmap			= gf_swr_mmap,
};

static int create_sw_region(struct kernfs_open_file *ctl_of, unsigned int id,
			    unsigned int numa_node)
{
	struct ghost_enclave *e = of_to_e(ctl_of);
	struct kernfs_node *dir, *swr_kn;
	struct ghost_sw_region *swr;
	char name[31];
	int err;

	dir = kernfs_find_and_get(e->enclave_dir, "sw_regions");
	if (WARN_ON_ONCE(!dir))
		return -EINVAL;

	if (snprintf(name, sizeof(name), "sw_%u", id) >= sizeof(name)) {
		err = -ENOSPC;
		goto err_snprintf;
	}

	swr_kn = kernfs_create_file_ns(dir, name, 0440, e->uid, e->gid, 0,
				       &gf_ops_e_swr, e, NULL);
	if (IS_ERR(swr_kn)) {
		err = PTR_ERR(swr_kn);
		goto err_create_kn;
	}
	/* swr_kn is inaccessible until kernfs_activate. */

	swr = ghost_create_sw_region(e, id, numa_node);
	if (IS_ERR(swr)) {
		err = PTR_ERR(swr);
		goto err_create_swr;
	}

	swr_kn->attr.size = swr->mmap_sz;
	swr_kn->priv = swr;
	kernfs_activate(swr_kn);

	return 0;
err_create_swr:
	kernfs_remove(swr_kn);
err_create_kn:
err_snprintf:
	kernfs_put(dir);
	return err;
}

static void generate_task_new(struct ghost_enclave *e, struct task_struct *p,
			      void *arg)
{
	struct rq_flags rf;
	struct rq *rq;

	rq = task_rq_lock(p, &rf);
	/*
	 * Make sure p is in the enclave.  It could have departed after we
	 * unlocked the enclave.  P could also have rejoined too, and it's OK
	 * to send another task_new.
	 */
	if (p->ghost.enclave == e)
		task_deliver_msg_task_new(rq, p, task_on_rq_queued(p));
	task_rq_unlock(rq, p, &rf);
}

static ssize_t gf_ctl_write(struct kernfs_open_file *of, char *buf,
			    size_t len, loff_t off)
{
	unsigned int arg1, arg2;
	int err, qfd;

	/*
	 * Ignore the offset for ctl commands, so userspace doesn't have to
	 * worry about lseeking after each command.  Userspace should submit a
	 * single write per command too, and not write("des"), write ("troy").
	 * Otherwise they'll fail.
	 */

	strip_slash_n(buf, len);

	if (!strcmp(buf, "destroy")) {
		destroy_enclave(of);
	} else if (sscanf(buf, "create sw_region %u %u", &arg1, &arg2) == 2) {
		err = create_sw_region(of, arg1, arg2);
		if (err)
			return err;
	} else if (sscanf(buf, "become agent %d", &qfd) == 1) {
		err = ctl_become_agent(of, qfd);
		if (err)
			return err;
	} else if (!strcmp(buf, "disable my bpf_prog_load")) {
		current->group_leader->ghost.bpf_cannot_load_prog = 1;
	} else if (!strcmp(buf, "discover tasks")) {
		err = enclave_for_each_task(of_to_e(of), generate_task_new,
					    NULL);
		if (err)
			return err;
	} else {
		pr_err("%s: bad cmd :%s:", __func__, buf);
		return -EINVAL;
	}

	return len;
}

static long enclave_ioctl(struct ghost_enclave *e, unsigned int cmd,
			  unsigned long arg)
{
	switch (cmd) {
	case GHOST_IOC_NULL:
		return 0;
	case GHOST_IOC_SW_GET_INFO:
		return ghost_sw_get_info(e,
				(struct ghost_ioc_sw_get_info __user *)arg);
	case GHOST_IOC_SW_FREE:
		return ghost_sw_free(e, (void __user *)arg);
	case GHOST_IOC_CREATE_QUEUE:
		return ghost_create_queue(e,
				(struct ghost_ioc_create_queue __user *)arg);
	case GHOST_IOC_ASSOC_QUEUE:
		return ghost_associate_queue(
				(struct ghost_ioc_assoc_queue __user *)arg);
	case GHOST_IOC_SET_DEFAULT_QUEUE:
		return ghost_set_default_queue(e,
			(struct ghost_ioc_set_default_queue __user *)arg);
	case GHOST_IOC_CONFIG_QUEUE_WAKEUP:
		return ghost_config_queue_wakeup(
			(struct ghost_ioc_config_queue_wakeup __user *)arg);
	case GHOST_IOC_GET_CPU_TIME:
		return ghost_get_cpu_time(
				(struct ghost_ioc_get_cpu_time __user *)arg);
	case GHOST_IOC_COMMIT_TXN:
		return ioctl_ghost_commit_txn(e,
				(struct ghost_ioc_commit_txn __user *)arg);
	case GHOST_IOC_SYNC_GROUP_TXN:
		return ghost_sync_group(e,
				(struct ghost_ioc_commit_txn __user *)arg);
	case GHOST_IOC_TIMERFD_SETTIME:
		return ghost_timerfd_settime(
				(struct ghost_ioc_timerfd_settime __user *)arg);
	case GHOST_IOC_RUN:
		return ghost_run(e, (struct ghost_ioc_run __user *)arg);
	}
	return -ENOIOCTLCMD;
}

static long gf_ctl_ioctl(struct kernfs_open_file *of, unsigned int cmd,
			 unsigned long arg)
{
	struct ghost_enclave *e = of_to_e(of);
	long ret;

	if (!(of->file->f_mode & FMODE_WRITE))
		return -EACCES;

	/*
	 * Active protection prevents gf_e_release from being called (and any
	 * mmaps from being unmapped, though that doesn't apply to ctl).  Active
	 * protection prevents the kn from being drained/deleted while we are
	 * operating on it.  It is meant for syscalls in progress, not held
	 * forever.  Some of these ioctls, e.g. ghost_run, can block for
	 * arbitrarily long.
	 *
	 * The only thing we use the kn for is to get a stable reference to e.
	 * We can just up the kref on our own, and ignore the kn.
	 */
	kref_get(&e->kref);
	kernfs_break_active_protection(of->kn);
	ret = enclave_ioctl(e, cmd, arg);
	kernfs_unbreak_active_protection(of->kn);
	kref_put(&e->kref, enclave_release);

	return ret;
}

static struct kernfs_ops gf_ops_e_ctl = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_ctl_show,
	.write			= gf_ctl_write,
	.ioctl			= gf_ctl_ioctl,
};

static int gf_deliver_ticks_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%d", READ_ONCE(e->deliver_ticks));
	return 0;
}

static ssize_t gf_deliver_ticks_write(struct kernfs_open_file *of,
				      char *buf, size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	int tunable;

	err = kstrtoint(buf, 0, &tunable);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->deliver_ticks, !!tunable);

	return len;
}

static struct kernfs_ops gf_ops_e_deliver_ticks = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_deliver_ticks_show,
	.write			= gf_deliver_ticks_write,
};

static int gf_live_dangerously_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%d", READ_ONCE(e->live_dangerously));
	return 0;
}

static ssize_t gf_live_dangerously_write(struct kernfs_open_file *of,
					 char *buf, size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	int tunable;

	err = kstrtoint(buf, 0, &tunable);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->live_dangerously, !!tunable);

	return len;
}

static struct kernfs_ops gf_ops_e_live_dangerously = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_live_dangerously_show,
	.write			= gf_live_dangerously_write,
};

/*
 * Returns a kreffed pointer for the enclave for f, if f is a ghostfs ctl file.
 * NULL otherwise.
 *
 * The kernfs_ops don't need this helper.  kernfs manages the the refcounts.  We
 * need to do it manually here, because this is is a "backdoor" function to get
 * the enclave pointer.  That pointer is kept alive by kernfs.
 */
static struct ghost_enclave *ctlfd_enclave_get_kref(int ctl_fd)
{
	struct fd fd;
	struct kernfs_node *kn;
	struct ghost_enclave *e = NULL;

	fd = fdget(ctl_fd);
	/*
	 * You can fdput even if there is no fd->file.
	 * You must fdput if there is a file.
	 */
	if (!fd.file)
		goto out_fdput;
	kn = kernfs_node_from_file(fd.file);
	if (!kn)
		goto out_fdput;
	if (kernfs_type(kn) != KERNFS_FILE)
		goto out_fdput;
	if (kn->attr.ops != &gf_ops_e_ctl)
		goto out_fdput;
	if (!kernfs_get_active(kn))
		goto out_fdput;
	e = kn->priv;
	if (e)
		kref_get(&e->kref);
	else
		WARN_ONCE(1, "ctlfd had no kn->priv!");
	/* We only need the active protection until we up the kref */
	kernfs_put_active(kn);

out_fdput:
	fdput(fd);
	return e;
}

static int gf_runnable_timeout_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%lld", ktime_to_ms(READ_ONCE(e->max_unscheduled)));
	return 0;
}

static ssize_t gf_runnable_timeout_write(struct kernfs_open_file *of, char *buf,
					 size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	unsigned long msec;

	err = kstrtoul(buf, 0, &msec);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->max_unscheduled, ms_to_ktime(msec));

	return len;
}

static struct kernfs_ops gf_ops_e_runnable_timeout = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_runnable_timeout_show,
	.write			= gf_runnable_timeout_write,
};

static int gf_status_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);
	unsigned long fl;
	bool is_active;
	unsigned long nr_tasks;

	/*
	 * Userspace uses this to find any active enclave, since they don't have
	 * any other methods yet to know which enclave to use.
	 */
	spin_lock_irqsave(&e->lock, fl);
	/*
	 * We don't need to lock to read agent_online, but eventually we'll
	 * check for the presence of an interstitial scheduler too.  This status
	 * is for the *enclave*, not the *agent*.
	 */
	is_active = e->agent_online;
	nr_tasks = e->nr_tasks;
	spin_unlock_irqrestore(&e->lock, fl);

	seq_printf(sf, "version %u\n", e->abi->version);
	seq_printf(sf, "active %s\n", is_active ? "yes" : "no");
	seq_printf(sf, "nr_tasks %lu\n", nr_tasks);
	return 0;
}

static struct kernfs_ops gf_ops_e_status = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_status_show,
};

static int gf_switchto_disabled_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%d", READ_ONCE(e->switchto_disabled));
	return 0;
}

static ssize_t gf_switchto_disabled_write(struct kernfs_open_file *of,
					  char *buf, size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	int tunable;

	err = kstrtoint(buf, 0, &tunable);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->switchto_disabled, !!tunable);

	return len;
}

static struct kernfs_ops gf_ops_e_switchto_disabled = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_switchto_disabled_show,
	.write			= gf_switchto_disabled_write,
};

static int gf_tasks_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);
	unsigned long irq_fl;
	struct task_struct *t;

	/* TODO: limited to PAGE_SIZE, fixable with seq_{start,next,stop.} */
	spin_lock_irqsave(&e->lock, irq_fl);
	list_for_each_entry(t, &e->task_list, ghost.task_list)
		seq_printf(sf, "%d\n", t->pid);
	spin_unlock_irqrestore(&e->lock, irq_fl);

	return 0;
}

/*
 * This file is world writable so that any task can join an enclave.  However,
 * you must have CAP_SYS_NICE to change the scheduling policy of another thread.
 * This is checked in the core sched_setscheduler code.
 */
static ssize_t gf_tasks_write(struct kernfs_open_file *of, char *buf,
			      size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	struct ghost_enclave *old_target;
	ssize_t ret;
	pid_t pid;
	struct task_struct *t;

	/* See _ghost_setscheduler() for the meaning of sched_priority. */
	struct sched_param param = {
		.sched_priority = -2,
	};

	ret = kstrtoint(buf, 0, &pid);
	if (ret)
		return ret;

	rcu_read_lock();
	if (pid) {
		t = find_task_by_vpid(pid);
		if (!t) {
			ret = -ESRCH;
			goto out;
		}
	} else {
		t = current;
	}

	old_target = set_target_enclave(e);
	ret = sched_setscheduler(t, SCHED_GHOST, &param);
	if (ret == 0)
		ret = len;
	restore_target_enclave(old_target);

out:
	rcu_read_unlock();

	return ret;
}

static struct kernfs_ops gf_ops_e_tasks = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_tasks_show,
	.write			= gf_tasks_write,
};

static int gf_wake_on_waker_cpu_show(struct seq_file *sf, void *v)
{
	struct ghost_enclave *e = seq_to_e(sf);

	seq_printf(sf, "%d", READ_ONCE(e->wake_on_waker_cpu));
	return 0;
}

static ssize_t gf_wake_on_waker_cpu_write(struct kernfs_open_file *of,
					  char *buf, size_t len, loff_t off)
{
	struct ghost_enclave *e = of_to_e(of);
	int err;
	int tunable;

	err = kstrtoint(buf, 0, &tunable);
	if (err)
		return -EINVAL;

	WRITE_ONCE(e->wake_on_waker_cpu, !!tunable);

	return len;
}

static struct kernfs_ops gf_ops_e_wake_on_waker_cpu = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_wake_on_waker_cpu_show,
	.write			= gf_wake_on_waker_cpu_write,
};

static struct gf_dirent enclave_dirtab[] = {
	{
		.name		= "sw_regions",
		.mode		= 0555,
		.is_dir		= true,
	},
	{
		.name		= "abi_version",
		.mode		= 0444,
		.ops		= &gf_ops_e_abi_version,
	},
	{
		.name		= "agent_online",
		.mode		= 0664,
		.ops		= &gf_ops_e_agent_online,
	},
	{
		.name		= "commit_at_tick",
		.mode		= 0664,
		.ops		= &gf_ops_e_commit_at_tick,
	},
	{
		.name		= "cpu_data",
		.mode		= 0660,
		.ops		= &gf_ops_e_cpu_data,
	},
	{
		.name		= "cpulist",
		.mode		= 0664,
		.ops		= &gf_ops_e_cpulist,
	},
	{
		.name		= "cpumask",
		.mode		= 0664,
		.ops		= &gf_ops_e_cpumask,
	},
	{
		.name		= "ctl",
		.mode		= 0664,
		.ops		= &gf_ops_e_ctl,
	},
	{
		.name		= "deliver_ticks",
		.mode		= 0664,
		.ops		= &gf_ops_e_deliver_ticks,
	},
	{
		.name		= "live_dangerously",
		.mode		= 0664,
		.ops		= &gf_ops_e_live_dangerously,
	},
	{
		.name		= "runnable_timeout",
		.mode		= 0664,
		.ops		= &gf_ops_e_runnable_timeout,
	},
	{
		.name		= "status",
		.mode		= 0444,
		.ops		= &gf_ops_e_status,
	},
	{
		.name		= "switchto_disabled",
		.mode		= 0664,
		.ops		= &gf_ops_e_switchto_disabled,
	},
	{
		.name		= "tasks",
		.mode		= 0666,
		.ops		= &gf_ops_e_tasks,
	},
	{
		.name		= "wake_on_waker_cpu",
		.mode		= 0664,
		.ops		= &gf_ops_e_wake_on_waker_cpu,
	},
	{0},
};

/* Caller is responsible for cleanup.  Removing the parent will suffice. */
static int gf_add_files(struct kernfs_node *parent, struct gf_dirent *dirtab,
			struct ghost_enclave *e)
{
	struct gf_dirent *gft;
	struct kernfs_node *kn;

	for (gft = dirtab; gft->name; gft++) {
		if (gft->is_dir) {
			kn = kernfs_create_dir_ns(parent, gft->name, gft->mode,
						  e->uid, e->gid, NULL, NULL);
		} else {
			kn = kernfs_create_file_ns(parent, gft->name, gft->mode,
						   e->uid, e->gid, gft->size,
						   gft->ops, e, NULL);
		}
		if (IS_ERR(kn))
			return PTR_ERR(kn);
	}
	return 0;
}

/*
 * Most gf_dirent file sizes are not known at compile time.  Most don't matter
 * for sysfs and we can leave them as 0.  But for anything that gets mmapped,
 * it's convenient for userspace for the kernel to say how big it is.
 */
static void runtime_adjust_dirtabs(void)
{
	struct gf_dirent *enc_txn;

	const loff_t GHOST_CPU_DATA_REGION_SIZE =
		sizeof(struct ghost_cpu_data) * num_possible_cpus();

	enc_txn = gf_find_file(enclave_dirtab, "cpu_data");
	if (WARN_ON(!enc_txn))
		return;
	enc_txn->size = GHOST_CPU_DATA_REGION_SIZE;
}

static int __init abi_init(const struct ghost_abi *abi)
{
	/*
	 * ghost bpf programs encode the ABI they were compiled against
	 * in the upper 16 bits of 'prog->expected_attach_type' which
	 * only works as long as GHOST_VERSION can fit within 16 bits.
	 *
	 * Ideally this would be in ghost_bpf_link_attach() but we cannot
	 * include the uapi header in ghost_core.c so we check it here.
	 */
	BUILD_BUG_ON(GHOST_VERSION > 0xFFFF);

	if (WARN_ON_ONCE(abi->version != GHOST_VERSION))
		return -EINVAL;

	runtime_adjust_dirtabs();
	return 0;
}

static kgid_t parse_cmd_gid(const char *cmd_extra)
{
	gid_t gid;
	kgid_t kgid = GLOBAL_ROOT_GID;
	int ret;

	/* sscanf will snarf the leading whitespace, unlike kstrtoint. */
	ret = sscanf(cmd_extra, "%u", &gid);
	if (ret == 1)
		kgid = KGIDT_INIT(gid);
	return kgid;
}

static struct ghost_enclave *create_enclave(const struct ghost_abi *abi,
					    struct kernfs_node *dir,
					    ulong id, const char *cmd_extra)
{
	bool vmalloc_failed = false;
	struct ghost_enclave *e;
	int cpu, ret;

	BUILD_BUG_ON(sizeof(struct ghost_cpu_data) != PAGE_SIZE);

	if (WARN_ON_ONCE(abi->version != GHOST_VERSION))
		return ERR_PTR(-EINVAL);

	e = kzalloc(sizeof(*e), GFP_KERNEL);
	if (e == NULL)
		return ERR_PTR(-ENOMEM);

	e->abi = abi;
	spin_lock_init(&e->lock);
	kref_init(&e->kref);
	INIT_LIST_HEAD(&e->sw_region_list);
	INIT_LIST_HEAD(&e->task_list);
	INIT_LIST_HEAD(&e->inhibited_task_list);
	INIT_LIST_HEAD(&e->ew.link);
	INIT_WORK(&e->task_reaper, enclave_reap_tasks);
	INIT_WORK(&e->enclave_actual_release, enclave_actual_release);
	INIT_WORK(&e->enclave_destroyer, enclave_destroyer);

	e->cpu_data = kcalloc(num_possible_cpus(),
			      sizeof(struct ghost_cpu_data *), GFP_KERNEL);
	if (!e->cpu_data) {
		kfree(e);
		return ERR_PTR(-ENOMEM);
	}

	for_each_possible_cpu(cpu) {
		e->cpu_data[cpu] = vmalloc_user_node_flags(PAGE_SIZE,
							   cpu_to_node(cpu),
							   GFP_KERNEL);
		if (e->cpu_data[cpu] == NULL) {
			vmalloc_failed = true;
			break;
		}
	}

	if (vmalloc_failed) {
		for_each_possible_cpu(cpu)
			vfree(e->cpu_data[cpu]);
		kfree(e->cpu_data);
		kfree(e);
		return ERR_PTR(-ENOMEM);
	}

	e->uid = current_euid();
	e->gid = parse_cmd_gid(cmd_extra);
	ret = ghostfs_set_ugid(dir, e->uid, e->gid);
	if (ret) {
		kref_put(&e->kref, enclave_release);
		return ERR_PTR(ret);
	}

	ret = gf_add_files(dir, enclave_dirtab, e);
	if (ret) {
		kref_put(&e->kref, enclave_release);
		return ERR_PTR(ret);
	}

	e->id = id;
	e->enclave_dir = dir;

	return e;
}

/*
 * Called at the start of every pick_next_task() via __schedule().
 */
static void pnt_prologue(struct rq *rq, struct task_struct *prev,
			 struct rq_flags *rf)
{
	struct ghost_enclave *e;

	rq->ghost.check_prev_preemption = ghost_produce_prev_msgs(rq, prev);
	if (unlikely(rq->ghost.ignore_prev_preemption)) {
		rq->ghost.check_prev_preemption = false;
		rq->ghost.ignore_prev_preemption = false;
	}

	/* a negative 'switchto_count' indicates end of the chain */
	rq->ghost.switchto_count = -rq->ghost.switchto_count;
	WARN_ON_ONCE(rq->ghost.switchto_count > 0);

	/*
	 * Lockless way to set must_resched, which kicks prev off cpu.  The
	 * agent knows the cpu_seqnum from the last message it received, e.g.
	 * the TASK_LATCHED when prev started to run.
	 */
	if (READ_ONCE(rq->ghost.prev_resched_seq) == rq->ghost.cpu_seqnum)
		rq->ghost.must_resched = true;

	rcu_read_lock();
	e = rcu_dereference(per_cpu(enclave, cpu_of(rq)));
	/* If there is a BPF program, this will unlock the RQ */
	if (e)
		ghost_bpf_pnt(e, rq, prev, rf);
	rcu_read_unlock();
}

/*
 * Called in the context switch path when switching from 'prev' to 'next'
 * (either via a normal schedule or switchto).
 */
static void prepare_task_switch(struct rq *rq, struct task_struct *prev,
				struct task_struct *next)
{
	struct ghost_status_word *agent_sw;

	if (rq->ghost.agent) {
		/*
		 * XXX pick_next_task_fair() can return 'rq->idle' via
		 * core_tag_pick_next_matching_rendezvous().
		 */
		agent_sw = rq->ghost.agent->ghost.status_word;
		if (!task_has_ghost_policy(next) && next != rq->idle) {
			ghost_sw_clear_flag(agent_sw, GHOST_SW_CPU_AVAIL);
			if (rq->ghost.run_flags & NEED_CPU_NOT_IDLE) {
				rq->ghost.run_flags &= ~NEED_CPU_NOT_IDLE;
				ghost_need_cpu_not_idle(rq, next);
			}
		} else {
			ghost_sw_set_flag(agent_sw, GHOST_SW_CPU_AVAIL);
		}
	}

	if (!task_has_ghost_policy(prev))
		goto done;

	/* Who watches the watchmen? */
	if (prev == rq->ghost.agent)
		goto done;

	/*
	 * An oncpu task may switch into ghost (e.g. via a third party calling
	 * sched_setscheduler(2)) while the rq->lock is dropped in one of the
	 * pick_next_task handlers (e.g. during CFS idle load balancing).
	 *
	 * It is not possible to distinguish this in _switched_to_ghost() so
	 * we resolve 'prev->ghost.new_task' here. Failing to do this has
	 * dire consequences if 'prev' is runnable since it will languish
	 * in the kernel forever (in contrast to a blocked task there is
	 * no trigger forthcoming to produce a TASK_NEW in the future).
	 */
	if (unlikely(prev->ghost.new_task)) {
		WARN_ON_ONCE(prev->ghost.yield_task);
		WARN_ON_ONCE(prev->ghost.blocked_task);

		/*
		 * We just produced TASK_NEW so no need to consider 'prev' for
		 * a preemption edge (see ghost_produce_prev_msgs for details).
		 */
		rq->ghost.check_prev_preemption = false;

		prev->ghost.new_task = false;
		ghost_task_new(rq, prev);
		ghost_wake_agent_of(prev);
	}

	/* If we're on the ghost.tasks list, then we're runnable. */
	if (!list_empty(&prev->ghost.run_list)) {
		/*
		 * Keep ghost.tasks sorted by last_runnable_at.  Whenever we set
		 * the time, we append to the tail.
		 */
		list_del_init(&prev->ghost.run_list);
		list_add_tail(&prev->ghost.run_list, &rq->ghost.tasks);
		prev->ghost.last_runnable_at = ktime_get();
	}

	if (rq->ghost.check_prev_preemption) {
		rq->ghost.check_prev_preemption = false;
		ghost_task_preempted(rq, prev);
		ghost_wake_agent_of(prev);
	}

done:
	/*
	 * Clear the ONCPU bit after producing the task state change msg
	 * (e.g. preempted). This guarantees that when a task is offcpu
	 * its 'task_barrier' is stable.
	 */
	if (task_has_ghost_policy(prev)) {
		struct ghost_status_word *prev_sw = prev->ghost.status_word;
		WARN_ON_ONCE(!(prev_sw->flags & GHOST_SW_TASK_ONCPU));
		ghost_sw_clear_flag(prev_sw, GHOST_SW_TASK_ONCPU);
	}

	/*
	 * CPU is switching to a non-ghost task while a task is latched.
	 *
	 * Treat this like latched_task preemption because we don't know when
	 * the CPU will be available again so no point in keeping it latched.
	 */
	if (rq->ghost.latched_task) {
		/*
		 * If 'next' was returned from pick_next_task_ghost() then
		 * 'latched_task' must have been cleared. Conversely if
		 * there is 'latched_task' then 'next' could not have
		 * been returned from pick_next_task_ghost().
		 */
		WARN_ON_ONCE(task_has_ghost_policy(next) &&
			     !is_agent(rq, next));
		ghost_latched_task_preempted(rq);

		/*
		 * XXX the WARN above is susceptible to a false-negative
		 * when pick_next_task_ghost returns the idle task. This
		 * is not the common case but it highlights that what we
		 * really need to check is the sched_class that produced
		 * 'next'.
		 */
	}

	if (task_has_ghost_policy(next) && !is_agent(rq, next))
		ghost_task_got_oncpu(rq, next);

	/*
	 * The last task in the chain scheduled (blocked/yielded/preempted).
	 */
	if (rq->ghost.switchto_count < 0)
		rq->ghost.switchto_count = 0;
}

static int bpf_wake_agent(int cpu)
{
	return ghost_wake_agent_on_check(cpu);
}

/*
 * Attempts to run gtid on cpu.  Returns 0 or -error.
 *
 * Called from BPF helpers.  The programs that can call those helpers are
 * explicitly allowed in ghost_sched_func_proto.
 */
static int bpf_run_gtid(s64 gtid, u32 task_barrier, int run_flags, int cpu)
{
	bool check_caller_enclave = (cpu != smp_processor_id());

	return __ghost_run_gtid_on(gtid, task_barrier, run_flags, cpu,
				   check_caller_enclave);
}

static int bpf_resched_cpu(int cpu, u64 cpu_seqnum)
{
	int this_cpu = smp_processor_id();
	struct rq *rq;

	if (cpu < 0)
		return -EINVAL;
	if (cpu >= nr_cpu_ids || !cpu_online(cpu))
		return -ERANGE;
	if (!check_same_enclave(this_cpu, cpu))
		return -EXDEV;

	rq = cpu_rq(cpu);
	WRITE_ONCE(rq->ghost.prev_resched_seq, cpu_seqnum);
	if (cpu == this_cpu) {
		set_tsk_need_resched(current);
		set_preempt_need_resched();
	} else {
		resched_cpu_unlocked(cpu);
	}

	return 0;
}

static bool ghost_sched_is_valid_access(int off, int size,
					enum bpf_access_type type,
					const struct bpf_prog *prog,
					struct bpf_insn_access_aux *info)
{
	/* The verifier guarantees that size > 0. */
	if (off < 0 || off + size > sizeof(struct bpf_ghost_sched)
	    || off % size)
		return false;

	return true;
}

static bool ghost_msg_is_valid_access(int off, int size,
				      enum bpf_access_type type,
				      const struct bpf_prog *prog,
				      struct bpf_insn_access_aux *info)
{
	/* The verifier guarantees that size > 0. */
	if (off < 0 || off + size > sizeof(struct bpf_ghost_msg) || off % size)
		return false;

	return true;
}

static int ghost_sched_pnt_attach(struct ghost_enclave *e,
				  struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	if (e->bpf_pnt) {
		spin_unlock_irqrestore(&e->lock, irq_fl);
		return -EBUSY;
	}
	rcu_assign_pointer(e->bpf_pnt, prog);
	spin_unlock_irqrestore(&e->lock, irq_fl);
	return 0;
}

static void ghost_sched_pnt_detach(struct ghost_enclave *e,
				   struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	rcu_replace_pointer(e->bpf_pnt, NULL, lockdep_is_held(&e->lock));
	spin_unlock_irqrestore(&e->lock, irq_fl);
}

static int ghost_msg_send_attach(struct ghost_enclave *e,
				 struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	if (e->bpf_msg_send) {
		spin_unlock_irqrestore(&e->lock, irq_fl);
		return -EBUSY;
	}
	rcu_assign_pointer(e->bpf_msg_send, prog);
	spin_unlock_irqrestore(&e->lock, irq_fl);
	return 0;
}

static void ghost_msg_send_detach(struct ghost_enclave *e,
				  struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	rcu_replace_pointer(e->bpf_msg_send, NULL, lockdep_is_held(&e->lock));
	spin_unlock_irqrestore(&e->lock, irq_fl);
}

static int bpf_link_attach(struct ghost_enclave *e, struct bpf_prog *prog,
			   int prog_type, int attach_type)
{
	int err;

	switch (prog_type) {
	case BPF_PROG_TYPE_GHOST_SCHED:
		switch (attach_type) {
		case BPF_GHOST_SCHED_PNT:
			err = ghost_sched_pnt_attach(e, prog);
			break;
		default:
			pr_warn("bad sched bpf attach_type %d", attach_type);
			err = -EINVAL;
			break;
		}
		break;
	case BPF_PROG_TYPE_GHOST_MSG:
		switch (attach_type) {
		case BPF_GHOST_MSG_SEND:
			err = ghost_msg_send_attach(e, prog);
			break;
		default:
			pr_warn("bad msg bpf attach_type %d", attach_type);
			err = -EINVAL;
			break;
		}
		break;
	default:
		pr_warn("bad bpf prog_type %d", prog_type);
		err = -EINVAL;
	}

	return err;
}

static void bpf_link_detach(struct ghost_enclave *e, struct bpf_prog *prog,
			    int prog_type, int attach_type)
{
	switch (prog_type) {
	case BPF_PROG_TYPE_GHOST_SCHED:
		switch (attach_type) {
		case BPF_GHOST_SCHED_PNT:
			ghost_sched_pnt_detach(e, prog);
			break;
		default:
			WARN_ONCE(1, "enclave %lu: unexpected bpf prog %d/%d",
				  e->id, prog_type, attach_type);
			break;
		}
		break;
	case BPF_PROG_TYPE_GHOST_MSG:
		switch (attach_type) {
		case BPF_GHOST_MSG_SEND:
			ghost_msg_send_detach(e, prog);
			break;
		default:
			WARN_ONCE(1, "enclave %lu: unexpected bpf prog %d/%d",
				  e->id, prog_type, attach_type);
			break;
		}
		break;
	default:
		WARN_ONCE(1, "enclave %lu: unexpected bpf prog %d/%d",
			  e->id, prog_type, attach_type);
		break;
	}
}

struct bpf_ghost_link {
	struct bpf_link	link;
	struct ghost_enclave *e;
	enum bpf_prog_type prog_type;
	enum bpf_attach_type ea_type;
};

static void bpf_ghost_link_dealloc(struct bpf_link *link)
{
	struct bpf_ghost_link *sc_link =
		container_of(link, struct bpf_ghost_link, link);

	kfree(sc_link);
}

static void bpf_ghost_link_release(struct bpf_link *link)
{
	struct bpf_ghost_link *sc_link =
		container_of(link, struct bpf_ghost_link, link);
	struct ghost_enclave *e = sc_link->e;

	if (WARN_ONCE(!e, "Missing enclave for bpf link ea_type %d!",
		      sc_link->ea_type))
		return;

	bpf_link_detach(e, link->prog, sc_link->prog_type, sc_link->ea_type);

	kref_put(&e->kref, enclave_release);
	sc_link->e = NULL;
}

static const struct bpf_link_ops bpf_ghost_link_ops = {
	.release = bpf_ghost_link_release,
	.dealloc = bpf_ghost_link_dealloc,
};

static int _ghost_bpf_link_attach(const union bpf_attr *attr,
				  struct bpf_prog *prog,
				  int ea_type, int ea_abi)
{
	struct bpf_link_primer link_primer;
	struct bpf_ghost_link *sc_link;
	struct ghost_enclave *e;
	int err;

	switch (prog->type) {
	case BPF_PROG_TYPE_GHOST_SCHED:
		switch (ea_type) {
		case BPF_GHOST_SCHED_PNT:
			break;
		default:
			return -EINVAL;
		}
		break;
	case BPF_PROG_TYPE_GHOST_MSG:
		switch (ea_type) {
		case BPF_GHOST_MSG_SEND:
			break;
		default:
			return -EINVAL;
		}
		break;
	default:
		return -EINVAL;
	}

	sc_link = kzalloc(sizeof(*sc_link), GFP_USER);
	if (!sc_link)
		return -ENOMEM;
	bpf_link_init(&sc_link->link, BPF_LINK_TYPE_UNSPEC,
		      &bpf_ghost_link_ops, prog);
	sc_link->prog_type = prog->type;
	sc_link->ea_type = ea_type;

	err = bpf_link_prime(&sc_link->link, &link_primer);
	if (err) {
		kfree(sc_link);
		return -EINVAL;
	}

	e = ctlfd_enclave_get_kref(attr->link_create.target_fd);
	if (!e) {
		/* bpf_link_cleanup() triggers .dealloc, but not .release. */
		bpf_link_cleanup(&link_primer);
		return -EBADF;
	}
	/* ABI bug for us to have a false positive fd->enclave lookup. */
	if (WARN_ON(ea_abi != enclave_abi(e))) {
		bpf_link_cleanup(&link_primer);
		kref_put(&e->kref, enclave_release);
		return -EBADF;
	}

	/*
	 * On success, sc_link will hold the kref we got from
	 * ctlfd_enclave_get_kref(), which will get put when the link's FD is
	 * closed (and thus bpf_link_put -> bpf_link_free -> our release).  This
	 * is similar to how ghostfs files hold a kref on the enclave.  Release
	 * is not called on failure.
	 */
	sc_link->e = e;
	err = bpf_link_attach(e, prog, prog->type, ea_type);
	if (err) {
		bpf_link_cleanup(&link_primer);
		kref_put(&e->kref, enclave_release);
		return err;
	}

	return bpf_link_settle(&link_primer);
}


DEFINE_GHOST_ABI(current_abi) = {
	.version = GHOST_VERSION,
	.abi_init = abi_init,
	.create_enclave = create_enclave,
	.enclave_release = enclave_release,
	.enclave_add_cpu = ___enclave_add_cpu,
	.setscheduler = _ghost_setscheduler,
	.fork = _ghost_sched_fork,
	.cleanup_fork = _ghost_sched_cleanup_fork,
	.wait_for_rendezvous = wait_for_rendezvous,
	.pnt_prologue = pnt_prologue,
	.prepare_task_switch = prepare_task_switch,
	.tick = tick_handler,
	.switchto = _ghost_switchto,
	.commit_greedy_txn = _commit_greedy_txn,
	.copy_process_epilogue = ghost_initialize_status_word,
	.cpu_idle = cpu_idle,
	.timerfd_triggered = _ghost_timerfd_triggered,
	.bpf_wake_agent = bpf_wake_agent,
	.bpf_run_gtid = bpf_run_gtid,
	.bpf_resched_cpu = bpf_resched_cpu,
	.ghost_sched_is_valid_access = ghost_sched_is_valid_access,
	.ghost_msg_is_valid_access = ghost_msg_is_valid_access,
	.bpf_link_attach = _ghost_bpf_link_attach,

	/* ghost_agent_sched_class callbacks */
	.pick_next_ghost_agent = pick_next_ghost_agent,

	/* ghost_sched_class callbacks */
	.update_curr = _update_curr_ghost,
	.prio_changed = _prio_changed_ghost,
	.switched_to = _switched_to_ghost,
	.switched_from = _switched_from_ghost,
	.task_dead = _task_dead_ghost,
	.dequeue_task = _dequeue_task_ghost,
	.put_prev_task = _put_prev_task_ghost,
	.enqueue_task = _enqueue_task_ghost,
	.set_next_task = _set_next_task_ghost,
	.task_tick = _task_tick_ghost,
	.pick_next_task = _pick_next_task_ghost,
	.check_preempt_curr = _check_preempt_curr_ghost,
	.yield_task = _yield_task_ghost,
#ifdef CONFIG_SMP
	.balance = _balance_ghost,
	.select_task_rq = _select_task_rq_ghost,
	.task_woken = _task_woken_ghost,
	.set_cpus_allowed = _set_cpus_allowed_ghost,
#endif
};

