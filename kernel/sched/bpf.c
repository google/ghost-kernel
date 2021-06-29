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

#include "sched.h"
#include <linux/filter.h>

#ifdef CONFIG_SCHED_CLASS_GHOST

BPF_CALL_2(bpf_ghost_wake_agent, struct bpf_ghost_sched_kern *, ctx, u32, cpu)
{
	return ghost_wake_agent_on_check(cpu);
}

static const struct bpf_func_proto bpf_ghost_wake_agent_proto = {
	.func		= bpf_ghost_wake_agent,
	.gpl_only	= true,
	.ret_type	= RET_INTEGER,
	.arg1_type	= ARG_PTR_TO_CTX,
	.arg2_type	= ARG_ANYTHING,
};

bool ghost_bpf_skip_tick(struct ghost_enclave *e, struct rq *rq)
{
	struct bpf_ghost_sched_kern ctx = {};
	struct bpf_prog *prog;

	lockdep_assert_held(&rq->lock);

	prog = rcu_dereference(e->bpf_tick);
	if (!prog)
		return false;

	/* prog returns 1 if we want a tick on this cpu. */
	return BPF_PROG_RUN(prog, &ctx) != 1;
}

static int ghost_sched_tick_attach(struct ghost_enclave *e,
				   struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	if (e->bpf_tick) {
		spin_unlock_irqrestore(&e->lock, irq_fl);
		return -EBUSY;
	}
	rcu_assign_pointer(e->bpf_tick, prog);
	spin_unlock_irqrestore(&e->lock, irq_fl);
	return 0;
}

static void ghost_sched_tick_detach(struct ghost_enclave *e,
				    struct bpf_prog *prog)
{
	unsigned long irq_fl;

	spin_lock_irqsave(&e->lock, irq_fl);
	rcu_replace_pointer(e->bpf_tick, NULL, lockdep_is_held(&e->lock));
	spin_unlock_irqrestore(&e->lock, irq_fl);
}

struct bpf_ghost_sched_link {
	struct bpf_link	link;
	struct ghost_enclave *e;
	enum bpf_attach_type ea_type;
};

static void bpf_ghost_sched_link_release(struct bpf_link *link)
{
	struct bpf_ghost_sched_link *sc_link =
		container_of(link, struct bpf_ghost_sched_link, link);
	struct ghost_enclave *e = sc_link->e;

	if (WARN_ONCE(!e, "Missing enclave for bpf link ea_type %d!",
		      sc_link->ea_type))
		return;

	switch (sc_link->ea_type) {
	case BPF_GHOST_SCHED_SKIP_TICK:
		ghost_sched_tick_detach(e, link->prog);
		break;
	default:
		WARN_ONCE(1, "Unexpected release for ea_type %d",
			  sc_link->ea_type);
		break;
	};
	kref_put(&e->kref, enclave_release);
	sc_link->e = NULL;
}

static void bpf_ghost_sched_link_dealloc(struct bpf_link *link)
{
	struct bpf_ghost_sched_link *sc_link =
		container_of(link, struct bpf_ghost_sched_link, link);

	kfree(sc_link);
}

static const struct bpf_link_ops bpf_ghost_sched_link_ops = {
	.release = bpf_ghost_sched_link_release,
	.dealloc = bpf_ghost_sched_link_dealloc,
};

int ghost_sched_bpf_link_attach(const union bpf_attr *attr,
				struct bpf_prog *prog)
{
	struct bpf_link_primer link_primer;
	struct bpf_ghost_sched_link *sc_link;
	enum bpf_attach_type ea_type;
	struct ghost_enclave *e;
	struct fd f_enc = {0};
	int err;

	if (attr->link_create.flags)
		return -EINVAL;
	if (prog->expected_attach_type != attr->link_create.attach_type)
		return -EINVAL;
	ea_type = prog->expected_attach_type;

	switch (ea_type) {
	case BPF_GHOST_SCHED_SKIP_TICK:
		break;
	default:
		return -EINVAL;
	};

	sc_link = kzalloc(sizeof(*sc_link), GFP_USER);
	if (!sc_link)
		return -ENOMEM;
	bpf_link_init(&sc_link->link, BPF_LINK_TYPE_UNSPEC,
		      &bpf_ghost_sched_link_ops, prog);
	sc_link->ea_type = ea_type;

	err = bpf_link_prime(&sc_link->link, &link_primer);
	if (err) {
		kfree(sc_link);
		return -EINVAL;
	}

	e = ghost_fdget_enclave(attr->link_create.target_fd, &f_enc);
	if (!e) {
		ghost_fdput_enclave(e, &f_enc);
		/* bpf_link_cleanup() triggers .dealloc, but not .release. */
		bpf_link_cleanup(&link_primer);
		return -EBADF;
	}
	/*
	 * On success, sc_link will hold a kref on the enclave, which will get
	 * put when the link's FD is closed (and thus bpf_link_put ->
	 * bpf_link_free -> our release).  This is similar to how ghostfs files
	 * hold a kref on the enclave.  Release is not called on failure.
	 */
	kref_get(&e->kref);
	sc_link->e = e;
	ghost_fdput_enclave(e, &f_enc);

	switch (ea_type) {
	case BPF_GHOST_SCHED_SKIP_TICK:
		err = ghost_sched_tick_attach(e, prog);
		break;
	default:
		pr_warn("bad sched bpf ea_type %d, should be unreachable",
			ea_type);
		err = -EINVAL;
		break;
	};
	if (err) {
		/* bpf_link_cleanup() triggers .dealloc, but not .release. */
		bpf_link_cleanup(&link_primer);
		kref_put(&e->kref, enclave_release);
		return err;
	}

	return bpf_link_settle(&link_primer);
}

/* netns does this to have a packed array of progs[type].  might do this for the
 * task type only, or maybe for all ghost types.
 */
enum ghost_sched_bpf_attach_type {
	GHOST_SCHED_BPF_INVALID = -1,
	GHOST_SCHED_BPF_TICK = 0,
	MAX_SCHED_BPF_ATTACH_TYPE
};

static inline enum ghost_sched_bpf_attach_type
to_ghost_sched_bpf_attach_type(enum bpf_attach_type attach_type)
{
	switch (attach_type) {
	case BPF_GHOST_SCHED_SKIP_TICK:
		return GHOST_SCHED_BPF_TICK;
	default:
		return GHOST_SCHED_BPF_INVALID;
	}
}

int ghost_sched_bpf_prog_attach(const union bpf_attr *attr,
				struct bpf_prog *prog)
{
	enum ghost_sched_bpf_attach_type type;

	if (attr->target_fd || attr->attach_flags || attr->replace_bpf_fd)
		return -EINVAL;
	type = to_ghost_sched_bpf_attach_type(attr->attach_type);
	if (type < 0)
		return -EINVAL;

	/* no task attachable types yet */

	return -1;
}

int ghost_sched_bpf_prog_detach(const union bpf_attr *attr,
				enum bpf_prog_type ptype)
{
	struct bpf_prog *prog;
	enum ghost_sched_bpf_attach_type type;

	if (attr->attach_flags)
		return -EINVAL;

	type = to_ghost_sched_bpf_attach_type(attr->attach_type);
	if (type < 0)
		return -EINVAL;

	prog = bpf_prog_get_type(attr->attach_bpf_fd, ptype);
	if (IS_ERR(prog))
		return PTR_ERR(prog);

	if (prog->expected_attach_type != attr->attach_type) {
		bpf_prog_put(prog);
		return -EINVAL;
	}

	/* no task attachable types yet */

	bpf_prog_put(prog);

	return -1;
}

static const struct bpf_func_proto *
ghost_sched_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	switch (func_id) {
	case BPF_FUNC_ghost_wake_agent:
		return &bpf_ghost_wake_agent_proto;
	default:
		return bpf_base_func_proto(func_id);
	}
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

	switch (off) {
	default:
		return false;
	}
}

#define SCHEDULER_ACCESS_FIELD(T, F)					\
	T(BPF_FIELD_SIZEOF(struct bpf_ghost_sched_kern, F),		\
	  si->dst_reg, si->src_reg,					\
	  offsetof(struct bpf_ghost_sched_kern, F))

static u32 ghost_sched_convert_ctx_access(enum bpf_access_type type,
					  const struct bpf_insn *si,
					  struct bpf_insn *insn_buf,
					  struct bpf_prog *prog,
					  u32 *target_size)
{
	struct bpf_insn *insn = insn_buf;

	switch (si->off) {
	default:
		*target_size = 0;
		break;
	}

	*target_size = sizeof(u32);

	return insn - insn_buf;
}

const struct bpf_verifier_ops ghost_sched_verifier_ops = {
	.get_func_proto		= ghost_sched_func_proto,
	.is_valid_access	= ghost_sched_is_valid_access,
	.convert_ctx_access	= ghost_sched_convert_ctx_access,
};

const struct bpf_prog_ops ghost_sched_prog_ops = {
};
#else /* !CONFIG_SCHED_CLASS_GHOST */

const struct bpf_verifier_ops ghost_sched_verifier_ops = {};
const struct bpf_prog_ops ghost_sched_prog_ops = {};

int ghost_sched_bpf_link_attach(const union bpf_attr *attr,
				struct bpf_prog *prog)
{
	return -EINVAL;
}

int ghost_sched_bpf_prog_attach(const union bpf_attr *attr,
				struct bpf_prog *prog)
{
	return -EINVAL;
}

int ghost_sched_bpf_prog_detach(const union bpf_attr *attr,
				enum bpf_prog_type ptype)
{
	return -EINVAL;
}

#endif /* !CONFIG_SCHED_CLASS_GHOST */
