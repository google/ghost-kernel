#include <linux/kernfs.h>

#define _GHOST_MAYBE_CONST
#include "sched.h"

/* The load contribution that CFS sees for a running ghOSt task */
unsigned long sysctl_ghost_cfs_load_added = 1024;

static struct kernfs_root *ghost_kfs_root;

extern const struct ghost_abi __begin_ghost_abi[];
extern const struct ghost_abi __end_ghost_abi[];

#define for_each_abi(abi) \
	for (abi = __begin_ghost_abi; abi < __end_ghost_abi; abi++)

/*
 * We do not want to make 'SG_COOKIE_CPU_BITS' larger than necessary so that
 * we can maximize the number of times a sequence counter can increment before
 * overflowing.
 */
#if (CONFIG_NR_CPUS < 2048)
#define SG_COOKIE_CPU_BITS	11
#else
#define SG_COOKIE_CPU_BITS	14
#endif
#define SG_COOKIE_CPU_SHIFT	(63 - SG_COOKIE_CPU_BITS)    /* MSB=0 */

static DEFINE_PER_CPU(int64_t, sync_group_cookie);

struct gf_dirent {
	char			*name;
	umode_t			mode;
	struct kernfs_ops	*ops;
	loff_t			size;
	bool			is_dir;
};

/* Helper for when you "echo foo > ctl" without the -n. */
static void gf_strip_slash_n(char *buf, size_t count)
{
	char *n = strnchr(buf, count, '\n');

	if (n)
		*n = '\0';
}

/* Helper to set the uid/gid of a kn */
int ghostfs_set_ugid(struct kernfs_node *kn, kuid_t uid, kgid_t gid)
{
	struct iattr iattr = { .ia_valid = ATTR_UID | ATTR_GID,
			       .ia_uid = uid,
			       .ia_gid = gid, };

	/*
	 * cgroup_kn_set_ugid() returns immediately if uid == gid == 0.  That
	 * will work if we know the old uid/gid are 0, such as when a file is
	 * first created (default is GLOBAL_ROOT, both when making a new attr as
	 * well as if there are no attrs).
	 *
	 * In case we reuse this function for changing a kn from something else
	 * back to GLOBAL_ROOT, always call kernfs_setattr().
	 */

	return kernfs_setattr(kn, &iattr);
}

static const struct ghost_abi *ghost_abi_lookup(uint version)
{
	const struct ghost_abi *abi;

	for_each_abi(abi) {
		if (abi->version == version)
			return abi;
	}

	return NULL;
}

static int make_enclave(struct kernfs_node *parent, unsigned long id,
			unsigned int version, const char *cmd_extra)
{
	struct kernfs_node *dir;
	struct ghost_enclave *e;
	const struct ghost_abi *abi;
	char name[31];

	abi = ghost_abi_lookup(version);
	if (!abi)
		return -ESRCH;

	if (snprintf(name, sizeof(name), "enclave_%lu", id) >= sizeof(name))
		return -ENOSPC;

	dir = kernfs_create_dir(parent, name, 0555, NULL);
	if (IS_ERR(dir))
		return PTR_ERR(dir);

	/*
	 * ghost_create_enclave() is mostly just "alloc and initialize".
	 * Anything done by it gets undone in enclave_release, and it is not
	 * discoverable, usable, or otherwise hooked into the kernel until
	 * kernfs_active().
	 */
	e = abi->create_enclave(abi, dir, id, cmd_extra);
	if (IS_ERR(e)) {
		kernfs_remove(dir);	/* recursive */
		return PTR_ERR(e);
	}

	WARN_ON_ONCE(e->abi != abi);

	/*
	 * Once the enclave has been activated, it is available to userspace and
	 * can be used for scheduling.  After that, we must destroy it by
	 * calling ghost_destroy_enclave(), not by releasing the reference.
	 */
	kernfs_activate(dir);	/* recursive */
	return 0;
}

static ssize_t gf_top_ctl_write(struct kernfs_open_file *of, char *buf,
				size_t len, loff_t off)
{
	struct kernfs_node *ctl = of->kn;
	struct kernfs_node *top_dir = ctl->parent;
	unsigned long x;
	unsigned int abi_num;
	int ret, so_far;

	gf_strip_slash_n(buf, len);

	/*
	 * Any extra spaces, digits, or characters beyond the abi_num are passed
	 * to the abi's create_enclave().
	 */
	ret = sscanf(buf, "create %lu %u%n", &x, &abi_num, &so_far);
	if (ret == 2) {
		ret = make_enclave(top_dir, x, abi_num, buf + so_far);
		return ret ? ret : len;
	}

	return -EINVAL;
}

static struct kernfs_ops gf_ops_top_ctl = {
	.write			= gf_top_ctl_write,
};

static int gf_top_version_show(struct seq_file *sf, void *v)
{
	const struct ghost_abi *abi;

	for_each_abi(abi)
		seq_printf(sf, "%u\n", abi->version);

	return 0;
}

static struct kernfs_ops gf_ops_top_version = {
	.seq_show		= gf_top_version_show,
};

static struct gf_dirent top_dirtab[] = {
	{
		.name		= "ctl",
		.mode		= 0660,
		.ops		= &gf_ops_top_ctl,
	},
	{
		.name		= "version",
		.mode		= 0444,
		.ops		= &gf_ops_top_version,
	},
	{0}
};

/* Caller is responsible for cleanup.  Removing the parent will suffice. */
static int gf_add_files(struct kernfs_node *parent, struct gf_dirent *dirtab,
			void *priv)
{
	struct gf_dirent *gft;
	struct kernfs_node *kn;

	for (gft = dirtab; gft->name; gft++) {
		if (gft->is_dir) {
			kn = kernfs_create_dir(parent, gft->name, gft->mode,
					       NULL);
		} else {
			kn = kernfs_create_file(parent, gft->name, gft->mode,
						gft->size, gft->ops, priv);
		}
		if (IS_ERR(kn))
			return PTR_ERR(kn);
	}
	return 0;
}

static void __init ghost_abi_init(void)
{
	const struct ghost_abi *abi;
	int ret;

	for_each_abi(abi) {
		ret = abi->abi_init(abi);
		if (ret) {
			WARN(true, "Skipping ghost abi %d due to error %d",
			     abi->version, ret);
			continue;
		}
	}
}

static int __init ghost_setup_root(void)
{
	int ret;
	struct kernfs_root *fs_root;

	fs_root = kernfs_create_root(NULL, KERNFS_ROOT_CREATE_DEACTIVATED |
				     KERNFS_ROOT_EXTRA_OPEN_PERM_CHECK, NULL);
	if (IS_ERR(fs_root))
		return PTR_ERR(fs_root);

	ret = gf_add_files(fs_root->kn, top_dirtab, NULL);
	if (ret) {
		kernfs_destroy_root(fs_root);
		return ret;
	}

	ghost_kfs_root = fs_root;

	ghost_abi_init();

	kernfs_activate(ghost_kfs_root->kn);

	return ret;
}

#include "../../fs/kernfs/kernfs-internal.h"

static int ghost_get_tree(struct fs_context *fc)
{
	int ret;

	/* Technically, this should be in uapi/linux/magic.h. */
	#define GHOST_SUPER_MAGIC 0xBAD1DEA2

	VM_BUG_ON(!ghost_kfs_root);
	ret = kernfs_get_tree(fc);
	if (ret)
		pr_err_once("Failed to mount ghostfs: %ld\n", ret);
	return ret;
}

static void ghost_fs_context_free(struct fs_context *fc)
{
	struct kernfs_fs_context *kfc = fc->fs_private;

	kernfs_free_fs_context(fc);
	kfree(kfc);
}

static const struct fs_context_operations ghost_fs_context_ops = {
	.free		= ghost_fs_context_free,
	.get_tree	= ghost_get_tree,
};

static int ghost_init_fs_context(struct fs_context *fc)
{
	struct kernfs_fs_context *kfc;

	kfc = kzalloc(sizeof(struct kernfs_fs_context), GFP_KERNEL);
	if (!kfc)
		return -ENOMEM;

	kfc->root = ghost_kfs_root;
	kfc->magic = GHOST_SUPER_MAGIC;
	fc->fs_private = kfc;
	fc->ops = &ghost_fs_context_ops;
	put_user_ns(fc->user_ns);
	fc->user_ns = get_user_ns(&init_user_ns);
	fc->global = true;
	return 0;
}

static void ghost_kill_sb(struct super_block *sb)
{
	kernfs_kill_sb(sb);
}

static struct file_system_type ghost_fs_type = {
	.name			= "ghost",
	.init_fs_context	= ghost_init_fs_context,
	.kill_sb		= ghost_kill_sb,
};

static int __init ghostfs_init(void)
{
	int ret = 0;

	ret = ghost_setup_root();
	if (ret)
		return ret;

	ret = sysfs_create_mount_point(fs_kobj, "ghost");
	if (ret)
		goto cleanup_root;

	ret = register_filesystem(&ghost_fs_type);
	if (ret)
		goto cleanup_mountpoint;

	return 0;

cleanup_mountpoint:
	sysfs_remove_mount_point(fs_kobj, "ghost");
cleanup_root:
	kernfs_destroy_root(ghost_kfs_root);
	ghost_kfs_root = NULL;

	return ret;
}

static void __exit ghostfs_exit(void)
{
	unregister_filesystem(&ghost_fs_type);
	sysfs_remove_mount_point(fs_kobj, "ghost");
	kernfs_destroy_root(ghost_kfs_root);
}

late_initcall(ghostfs_init);
__exitcall(ghostfs_exit);

/* per_cpu(enclave) write protected by 'cpu_rsvp' */
static DEFINE_SPINLOCK(cpu_rsvp);
DEFINE_PER_CPU_READ_MOSTLY(struct ghost_enclave *, enclave);

struct ghost_enclave *get_target_enclave(void)
{
	return current->ghost.__target_enclave;
}

struct ghost_enclave *set_target_enclave(struct ghost_enclave *e)
{
	struct ghost_enclave *old = current->ghost.__target_enclave;

	current->ghost.__target_enclave = e;
	return old;
}

void restore_target_enclave(struct ghost_enclave *old)
{
	current->ghost.__target_enclave = old;
}

/* Caller holds e->lock.  Either all cpus are added, or none are. */
int ghost_add_cpus(struct ghost_enclave *e, const struct cpumask *new_cpus)
{
	int cpu;

	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);

	for_each_cpu(cpu, new_cpus) {
		/*
		 * Let's make sure that 'cpu' hasn't been already claimed by
		 * another enclave.
		 */
		if (per_cpu(enclave, cpu)) {
			spin_unlock(&cpu_rsvp);
			return -EBUSY;
		}
	}

	for_each_cpu(cpu, new_cpus)
		e->abi->enclave_add_cpu(e, cpu);

	for_each_cpu(cpu, new_cpus)
		rcu_assign_pointer(per_cpu(enclave, cpu), e);

	spin_unlock(&cpu_rsvp);
	return 0;
}

void ghost_remove_cpu(struct ghost_enclave *e, int cpu)
{
	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);
	WARN_ON_ONCE(per_cpu(enclave, cpu) != e);
	rcu_assign_pointer(per_cpu(enclave, cpu), NULL);
	spin_unlock(&cpu_rsvp);
}

/*
 * A sync-group cookie uniquely identifies a sync-group commit.
 *
 * It is useful to identify the initiator and participants of the sync-group.
 */
int64_t ghost_sync_group_cookie(void)
{
	int64_t val;

	WARN_ON_ONCE(preemptible());
	BUILD_BUG_ON(NR_CPUS > (1U << SG_COOKIE_CPU_BITS));

	val = __this_cpu_inc_return(sync_group_cookie);
	VM_BUG_ON((val <= 0) || (val & GHOST_POISONED_RENDEZVOUS));

	return val;
}

void ghost_wait_for_rendezvous(struct rq *rq)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(rq != this_rq());

	/* rcu_read_lock_sched() not needed; preemption is disabled. */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));

	if (WARN_ON_ONCE(!e))
		return;

	e->abi->wait_for_rendezvous(rq);
}

static struct ghost_enclave *_ghost_resolve_enclave(struct rq *rq,
						    struct task_struct *p)
{
	struct ghost_enclave *rq_enclave, *task_enclave;

	VM_BUG_ON(preemptible());

	/* Implicit read-side critical section due to disabled preemption */
	rq_enclave = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));

	/*
	 * Caller is responsible for ensuring stability of 'p->ghost.enclave'.
	 * This usually happens as a side-effect of holding 'rq->lock' of the
	 * cpu where the task is queued or running.
	 */
	task_enclave = p->ghost.enclave;
	WARN_ON_ONCE(!task_enclave && ghost_class(p->sched_class));

	/*
	 * XXX it is possible for a running task to enter ghost into enclave X
	 * while the cpu it is running on belongs to enclave Y. This is not
	 * supported properly yet hence the VM_BUG_ON.
	 */
#if 0	// FIXME(b/218869667)
	VM_BUG_ON(rq_enclave && task_enclave && rq_enclave != task_enclave);
#else
	VM_BUG_ON(rq_enclave && task_enclave &&
		  rq_enclave->abi != task_enclave->abi);
#endif

	/*
	 * 'rq_enclave' may be NULL if a running task enters ghost on a cpu
	 * that does not belong to any enclave.
	 */
	return rq_enclave ? rq_enclave : task_enclave;
}

void ghost_pnt_prologue(struct rq *rq, struct task_struct *prev,
			struct rq_flags *rf)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, prev);

	VM_BUG_ON(rq != this_rq());

	if (e != NULL)
		e->abi->pnt_prologue(rq, prev, rf);
}

void __init init_sched_ghost_class(void)
{
	int64_t cpu;

	for_each_possible_cpu(cpu)
		per_cpu(sync_group_cookie, cpu) = cpu << SG_COOKIE_CPU_SHIFT;
}

int ghost_setscheduler(struct task_struct *p, struct rq *rq,
		       const struct sched_attr *attr,
		       int *reset_on_fork)
{
	struct ghost_enclave *e;
	int oldpolicy = p->policy;
	int newpolicy = attr->sched_policy;

	if (WARN_ON_ONCE(!ghost_policy(oldpolicy) && !ghost_policy(newpolicy)))
		return -EINVAL;

	/*
	 * If the process is dying, finish_task_switch will call task_dead
	 * *after* releasing the rq lock.  We don't know if task_dead was called
	 * yet, and it will be called without holding any locks.  This can break
	 * ghost for both task scheduling into ghost and out of ghost.
	 * - If we're entering ghost, but already ran task_dead from our old
	 *   sched class, then we'll never run ghost_task_dead.
	 * - If we're leaving ghost, we need to run either ghost_task_dead xor
	 *   setscheduler from ghost, but we have no nice way of knowing if we
	 *   already ran ghost_task_dead.
	 */
	if (p->state == TASK_DEAD)
		return -ESRCH;

	/* Cannot change attributes for a ghost task after creation. */
	if (oldpolicy == newpolicy)
		return -EPERM;

	if (ghost_policy(oldpolicy)) {
		e = p->ghost.enclave;
		WARN_ON_ONCE(!e);
	} else {
		e = get_target_enclave();
	}

	/* Callers from sys_sched_setscheduler will not have e set. */
	if (!e)
		return -EBADF;

	return e->abi->setscheduler(e, p, rq, attr, reset_on_fork);
}

void ghost_prepare_task_switch(struct rq *rq, struct task_struct *prev,
			       struct task_struct *next)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, prev);

	VM_BUG_ON(rq != this_rq());

	if (e != NULL)
		e->abi->prepare_task_switch(rq, prev, next);
}

void ghost_cpu_idle(void)
{
	struct ghost_enclave *e;
	struct rq *rq = this_rq();

	WARN_ON_ONCE(preemptible());
	WARN_ON_ONCE(current != rq->idle);

	/* rcu_read_lock_sched() not needed; preemption is disabled. */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));

	if (e)
		e->abi->cpu_idle(rq);
}

unsigned long ghost_cfs_added_load(struct rq *rq)
{
	int ghost_nr_running = rq->ghost.ghost_nr_running;
	struct task_struct *curr;
	bool add_load = false;

	/* No ghost tasks; nothing to contribute load. */
	if (!ghost_nr_running)
		return 0;

	/*
	 * We have a few cases where we want to add load:
	 * (a): We have a local agent that is not blocked_in_run.
	 * (b): Currently have a non-agent ghost task running.
	 * (c): Have a latched task that is not yet running. We
	 * treat this the same as case (b), since this is really
	 * just a race over getting through schedule() (modulo possible
	 * preemption by another sched_class).
	 */

	if (ghost_nr_running > __ghost_extra_nr_running(rq)) {
		/* (a) */
		add_load = true;
		goto out;
	}

	rcu_read_lock();
	curr = READ_ONCE(rq->curr);
	if (task_has_ghost_policy(curr) && !is_agent(rq, curr) &&
	    curr->state == TASK_RUNNING) {
		/* (b) */
		add_load = true;
	}
	curr = NULL; /* don't use outside of RCU */
	rcu_read_unlock();
	if (add_load)
		goto out;

	if (rq->ghost.latched_task) {
		/* (c) */
		add_load = true;
	}

out:
	if (add_load)
		return sysctl_ghost_cfs_load_added;
	return 0;
}

int64_t ghost_alloc_gtid(struct task_struct *p)
{
	gtid_t gtid;
	uint64_t seqnum;

	static atomic64_t gtid_seqnum = ATOMIC64_INIT(0);

	BUILD_BUG_ON(PID_MAX_LIMIT != (1UL << GHOST_TID_PID_BITS));

	do {
		seqnum = atomic64_add_return(1, &gtid_seqnum) &
				((1UL << GHOST_TID_SEQNUM_BITS) - 1);
	} while (!seqnum);

	gtid = ((gtid_t)p->pid << GHOST_TID_SEQNUM_BITS) | seqnum;
	WARN_ON_ONCE(gtid <= 0);
	return gtid;
}

void ghost_copy_process_epilogue(struct task_struct *p)
{
	struct ghost_enclave *e = p->ghost.enclave;

	if (WARN_ON_ONCE(!e))
		return;

	e->abi->copy_process_epilogue(p);
}

/*
 * Called from the timer tick handler after dropping rq->lock.  Called
 * regardless of whether a ghost task is current or not.
 */
void ghost_tick(struct rq *rq)
{
	struct ghost_enclave *e;

	WARN_ON_ONCE(preemptible());
	WARN_ON_ONCE(rq != this_rq());

	/*
	 * Implicit read-side critical section since we are in hardirq context
	 * with interrupts disabled.
	 */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));

	if (e)
		e->abi->tick(e, rq);
}

/*
 * TODO(multi-enclave):
 * This should be done entirely within an ABI when a cpu is assigned
 * to the corresponding enclave. However because we allow tasks to enter
 * ghost on on arbitrary cpus (e.g. outside an enclave) then 'rq->ghost'
 * must be properly initialized on those cpus as well.
 */
void init_ghost_rq(struct ghost_rq *ghost_rq)
{
	INIT_LIST_HEAD(&ghost_rq->tasks);
	INIT_LIST_HEAD(&ghost_rq->enclave_work);
	WRITE_ONCE(ghost_rq->prev_resched_seq, ~0ULL);
}

int ghost_sched_fork(struct task_struct *p)
{
	int ret;
	struct rq *rq;
	struct rq_flags rf;
	struct ghost_enclave *e;

	VM_BUG_ON(!task_has_ghost_policy(p));

	/*
	 * Another task could be attempting to setsched current out of ghOSt.
	 * To keep current's enclave valid, we synchronize with the RQ lock.
	 */
	rq = task_rq_lock(current, &rf);
	if (!ghost_policy(current->policy)) {
		task_rq_unlock(rq, current, &rf);
		/* It's not quite ECHILD, but it'll tell us where to look. */
		return -ECHILD;
	}
	e = current->ghost.enclave;
	VM_BUG_ON(!e);
	kref_get(&e->kref);				/* get a local ref */
	task_rq_unlock(rq, current, &rf);

	ret = e->abi->fork(e, p);
	kref_put(&e->kref, e->abi->enclave_release);	/* release local ref */

	return ret;
}

void ghost_sched_cleanup_fork(struct task_struct *p)
{
	struct ghost_enclave *e = p->ghost.enclave;

	VM_BUG_ON(!task_has_ghost_policy(p));
	VM_BUG_ON(!e);

	e->abi->cleanup_fork(e, p);
}

void ghost_commit_greedy_txn(void)
{
	struct ghost_enclave *e;
	int cpu = get_cpu();

	VM_BUG_ON(preemptible());

	/* Implicit read-side critical section due to disabled preemption */
	e = rcu_dereference_sched(per_cpu(enclave, cpu));
	if (e)
		e->abi->commit_greedy_txn(cpu);

	put_cpu();
}

/* Called from timerfd_triggered() on timer expiry */
void ghost_timerfd_triggered(struct __kernel_timerfd_ghost *ktfd)
{
	int cpu = ktfd->cpu;
	struct ghost_enclave *e;

	if (WARN_ON_ONCE(cpu < 0 || cpu >= nr_cpu_ids || !cpu_online(cpu)))
		return;

	if (WARN_ON_ONCE(!ktfd->enabled))
		return;

	/*
	 * XXX the enclave lookup doesn't handle cpus moving out of enclaves
	 * properly (for e.g. a timerfd might be triggered on a cpu that is
	 * not associated with the enclave).
	 */
	rcu_read_lock();
	e = rcu_dereference(per_cpu(enclave, cpu));
	if (e)
		e->abi->timerfd_triggered(cpu, ktfd->type, ktfd->cookie);
	else
		WARN_ONCE(true, "cpu %d has no enclave", cpu);
	rcu_read_unlock();
}

static struct task_struct *pick_next_ghost_agent(struct rq *rq)
{
	struct task_struct *next;
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(rq != this_rq());

	/* Implicit read-side critical section due to disabled preemption */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));
	if (e)
		next = e->abi->pick_next_ghost_agent(rq);
	else
		next = NULL;

	return next;
}

static int balance_agent(struct rq *rq, struct task_struct *prev,
			 struct rq_flags *rf)
{
	return 0;
}

/*
 * An interstitial sched class that operates below the stop_sched_class. It
 * enables returning to an agent at the highest priority when the agent is about
 * to lose its CPU to another sched class. This allows the agent to transition
 * to another CPU before giving up its CPU.
 */
DEFINE_SCHED_CLASS(ghost_agent) = {
	.pick_next_task		= pick_next_ghost_agent,
#ifdef CONFIG_SMP
	.balance		= balance_agent,
#endif
};

static void update_curr_ghost(struct rq *rq)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, rq->curr);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->update_curr(rq);
}

static void prio_changed_ghost(struct rq *rq, struct task_struct *p, int old)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&p->pi_lock);
	lockdep_assert_held(&rq->lock);

	e = p->ghost.enclave;
	if (e)
		e->abi->prio_changed(rq, p, old);
	else
		WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
}

static void switched_to_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&p->pi_lock);
	lockdep_assert_held(&rq->lock);

	e = p->ghost.enclave;
	if (e)
		e->abi->switched_to(rq, p);
	else
		WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
}

static void switched_from_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&p->pi_lock);
	lockdep_assert_held(&rq->lock);

	e = p->ghost.enclave;
	if (e)
		e->abi->switched_from(rq, p);
	else
		WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
}

static void task_dead_ghost(struct task_struct *p)
{
	struct ghost_enclave *e;

	/*
	 * This looks risky since neither 'p->pi_lock' nor 'rq->lock' is held
	 * at this point but is safe because 'p' is no longer reachable from
	 * userspace at this point (it lost identity much earlier in do_exit).
	 *
	 * The only thing that can mutate 'p->ghost.enclave' is moving out of
	 * ghost but that cannot happen for the reason stated above.
	 */
	e = p->ghost.enclave;

	if (e)
		e->abi->task_dead(p);
	else
		WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
}

static void dequeue_task_ghost(struct rq *rq, struct task_struct *p, int flags)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->dequeue_task(rq, p, flags);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static void put_prev_task_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->put_prev_task(rq, p);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static void enqueue_task_ghost(struct rq *rq, struct task_struct *p, int flags)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->enqueue_task(rq, p, flags);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static void set_next_task_ghost(struct rq *rq, struct task_struct *p, bool first)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->set_next_task(rq, p, first);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

/*
 * Called from the timer tick handler while holding the rq->lock.  Called only
 * if a ghost task is current.
 */
static void task_tick_ghost(struct rq *rq, struct task_struct *p, int queued)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->task_tick(rq, p, queued);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static struct task_struct *pick_next_task_ghost(struct rq *rq)
{
	struct task_struct *next;
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(rq != this_rq());

	/* Implicit read-side critical section due to disabled preemption */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));
	if (e)
		next = e->abi->pick_next_task(rq);
	else
		next = NULL;

	return next;
}

static void check_preempt_curr_ghost(struct rq *rq, struct task_struct *p,
			      int wake_flags)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->check_preempt_curr(rq, p, wake_flags);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static void yield_task_ghost(struct rq *rq)
{
	struct task_struct *p = current;
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	VM_BUG_ON(rq != this_rq());
	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->yield_task(rq);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

int select_task_rq_ghost(struct task_struct *p, int cpu, int wake_flags)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&p->pi_lock);

	e = p->ghost.enclave;
	if (e)
		return e->abi->select_task_rq(p, cpu, wake_flags);

	WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
	return 0;
}

static int balance_ghost(struct rq *rq, struct task_struct *prev,
			 struct rq_flags *rf)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(rq != this_rq());

	/* Implicit read-side critical section due to disabled preemption */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));
	if (e)
		return e->abi->balance(rq, prev, rf);

	return -1;
}

void task_woken_ghost(struct rq *rq, struct task_struct *p)
{
	struct ghost_enclave *e = _ghost_resolve_enclave(rq, p);

	lockdep_assert_held(&rq->lock);

	if (e)
		e->abi->task_woken(rq, p);
	else
		WARN_ONCE(1, "task %d/%s without enclave on cpu %d",
			  p->pid, p->comm, cpu_of(rq));
}

static void set_cpus_allowed_ghost(struct task_struct *p,
			    const struct cpumask *newmask, u32 flags)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&p->pi_lock);

	e = p->ghost.enclave;
	if (e)
		e->abi->set_cpus_allowed(p, newmask, flags);
	else
		WARN_ONCE(1, "task %d/%s without enclave", p->pid, p->comm);
}

DEFINE_SCHED_CLASS(ghost) = {
	.update_curr		= update_curr_ghost,
	.prio_changed		= prio_changed_ghost,
	.switched_to		= switched_to_ghost,
	.switched_from		= switched_from_ghost,
	.task_dead		= task_dead_ghost,
	.dequeue_task		= dequeue_task_ghost,
	.put_prev_task		= put_prev_task_ghost,
	.enqueue_task		= enqueue_task_ghost,
	.set_next_task		= set_next_task_ghost,
	.task_tick		= task_tick_ghost,
	.pick_next_task		= pick_next_task_ghost,
	.check_preempt_curr	= check_preempt_curr_ghost,
	.yield_task		= yield_task_ghost,
#ifdef CONFIG_SMP
	.balance		= balance_ghost,
	.select_task_rq		= select_task_rq_ghost,
	.task_woken		= task_woken_ghost,
	.set_cpus_allowed	= set_cpus_allowed_ghost,
#endif
};

#ifdef CONFIG_SWITCHTO_API
void ghost_switchto(struct rq *rq, struct task_struct *prev,
		    struct task_struct *next, int switchto_flags)
{
	struct ghost_enclave *e;

	lockdep_assert_held(&rq->lock);
	VM_BUG_ON(prev != rq->curr);
	VM_BUG_ON(prev->state == TASK_RUNNING);
	VM_BUG_ON(next->state == TASK_RUNNING);
	VM_BUG_ON(!ghost_class(prev->sched_class));
	VM_BUG_ON(!ghost_class(next->sched_class));
	VM_BUG_ON(prev->ghost.enclave != next->ghost.enclave);
	VM_BUG_ON(!next->ghost.enclave);

	e = next->ghost.enclave;
	e->abi->switchto(rq, prev, next, switchto_flags);
}
#endif

#ifdef CONFIG_BPF
#include <linux/filter.h>

/*
 * ghost bpf programs encode the ABI they were compiled against in the
 * upper 16 bits of 'prog->expected_attach_type'.
 */
static inline int bpf_prog_eat_abi(const struct bpf_prog *prog)
{
	return (u32)prog->expected_attach_type >> 16;
}

static inline int bpf_prog_eat_type(const struct bpf_prog *prog)
{
	return prog->expected_attach_type & 0xFFFF;
}

BPF_CALL_1(bpf_ghost_wake_agent, u32, cpu)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());

	/*
	 * Each BPF helper has a corresponding integer in uapi/linux/bpf.h,
	 * similar to syscall numbers.  Catch any ABI inconsistencies between
	 * prodkernel and open source.
	 */
	BUILD_BUG_ON(BPF_FUNC_ghost_wake_agent != 3000);

	e = get_target_enclave();

	/* Paranoia: this is not expected */
	if (WARN_ON_ONCE(!e))
		return -ENODEV;

	return e->abi->bpf_wake_agent(cpu);
}

static const struct bpf_func_proto bpf_ghost_wake_agent_proto = {
	.func		= bpf_ghost_wake_agent,
	.gpl_only	= true,
	.ret_type	= RET_INTEGER,
	.arg1_type	= ARG_ANYTHING,
};

BPF_CALL_3(bpf_ghost_run_gtid, s64, gtid, u32, task_barrier, int, run_flags)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());

	/*
	 * Each BPF helper has a corresponding integer in uapi/linux/bpf.h,
	 * similar to syscall numbers.  Catch any ABI inconsistencies between
	 * prodkernel and open source.
	 */
	BUILD_BUG_ON(BPF_FUNC_ghost_run_gtid != 3001);

	e = get_target_enclave();

	/* Paranoia: this is not expected */
	if (WARN_ON_ONCE(!e))
		return -ENODEV;

	return e->abi->bpf_run_gtid(gtid, task_barrier, run_flags,
				    smp_processor_id());
}

static const struct bpf_func_proto bpf_ghost_run_gtid_proto = {
	.func		= bpf_ghost_run_gtid,
	.gpl_only	= true,
	.ret_type	= RET_INTEGER,
	.arg1_type	= ARG_ANYTHING,
	.arg2_type	= ARG_ANYTHING,
	.arg3_type	= ARG_ANYTHING,
};

BPF_CALL_2(bpf_ghost_resched_cpu, u32, cpu, u64, cpu_seqnum)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());

	BUILD_BUG_ON(BPF_FUNC_ghost_resched_cpu != 3002);

	e = get_target_enclave();

	/* Paranoia: this is not expected */
	if (WARN_ON_ONCE(!e))
		return -ENODEV;

	return e->abi->bpf_resched_cpu(cpu, cpu_seqnum);
}

static const struct bpf_func_proto bpf_ghost_resched_cpu_proto = {
	.func		= bpf_ghost_resched_cpu,
	.gpl_only	= true,
	.ret_type	= RET_INTEGER,
	.arg1_type	= ARG_ANYTHING,
	.arg2_type	= ARG_ANYTHING,
};

static const struct bpf_func_proto *
ghost_sched_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	int eat = bpf_prog_eat_type(prog);

	/* ghost func_ids are not in enum bpf_func_id */
	switch ((int)func_id) {
	case BPF_FUNC_ghost_wake_agent:
		return &bpf_ghost_wake_agent_proto;
	case BPF_FUNC_ghost_run_gtid:
		switch (eat) {
		case BPF_GHOST_SCHED_PNT:
			return &bpf_ghost_run_gtid_proto;
		default:
			return NULL;
		}
	case BPF_FUNC_ghost_resched_cpu:
		return &bpf_ghost_resched_cpu_proto;
	default:
		return bpf_base_func_proto(func_id);
	}
}

static bool ghost_sched_is_valid_access(int off, int size,
					enum bpf_access_type type,
					const struct bpf_prog *prog,
					struct bpf_insn_access_aux *info)
{
	int version = bpf_prog_eat_abi(prog);
	const struct ghost_abi *abi = ghost_abi_lookup(version);

	if (!abi)
		return false;

	return abi->ghost_sched_is_valid_access(off, size, type, prog, info);
}

const struct bpf_verifier_ops ghost_sched_verifier_ops = {
	.get_func_proto		= ghost_sched_func_proto,
	.is_valid_access	= ghost_sched_is_valid_access,
};

const struct bpf_prog_ops ghost_sched_prog_ops = {};

static const struct bpf_func_proto *
ghost_msg_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	/* ghost func_ids are not in enum bpf_func_id */
	switch ((int)func_id) {
	case BPF_FUNC_ghost_wake_agent:
		return &bpf_ghost_wake_agent_proto;
	case BPF_FUNC_ghost_resched_cpu:
		return &bpf_ghost_resched_cpu_proto;
	default:
		return bpf_base_func_proto(func_id);
	}
}

static bool ghost_msg_is_valid_access(int off, int size,
				      enum bpf_access_type type,
				      const struct bpf_prog *prog,
				      struct bpf_insn_access_aux *info)
{
	int version = bpf_prog_eat_abi(prog);
	const struct ghost_abi *abi = ghost_abi_lookup(version);

	if (!abi)
		return false;

	return abi->ghost_msg_is_valid_access(off, size, type, prog, info);
}

const struct bpf_verifier_ops ghost_msg_verifier_ops = {
	.get_func_proto		= ghost_msg_func_proto,
	.is_valid_access	= ghost_msg_is_valid_access,
};

const struct bpf_prog_ops ghost_msg_prog_ops = {};

int ghost_bpf_link_attach(const union bpf_attr *attr, struct bpf_prog *prog)
{
	const struct ghost_abi *abi;
	enum bpf_attach_type ea_type;
	int ea_abi;

	ea_type = bpf_prog_eat_type(prog);
	ea_abi = bpf_prog_eat_abi(prog);
	if (attr->link_create.flags)
		return -EINVAL;
	if (prog->expected_attach_type != attr->link_create.attach_type)
		return -EINVAL;

	abi = ghost_abi_lookup(ea_abi);
	if (!abi)
		return -EBADF;
	return abi->bpf_link_attach(attr, prog, ea_type, ea_abi);
}
#endif
