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

static DEFINE_MUTEX(sched_tick);
static struct bpf_prog *tick_prog;

bool bpf_sched_ghost_skip_tick(void)
{
	struct bpf_scheduler_kern ctx = {};
	struct bpf_prog *prog;
	int ret;

	rcu_read_lock();

	prog = rcu_dereference(tick_prog);
	if (!prog) {
		rcu_read_unlock();
		return false;
	}

	/* prog returns 1 if we want a tick on this cpu. */
	ret = BPF_PROG_RUN(prog, &ctx);

	rcu_read_unlock();

	return ret != 1;
}

static int sched_tick_attach(struct bpf_prog *prog)
{
	mutex_lock(&sched_tick);
	if (tick_prog) {
		mutex_unlock(&sched_tick);
		return -EBUSY;
	}
	rcu_assign_pointer(tick_prog, prog);
	mutex_unlock(&sched_tick);
	return 0;
}

static void sched_tick_detach(struct bpf_prog *prog)
{
	mutex_lock(&sched_tick);
	rcu_replace_pointer(tick_prog, NULL, lockdep_is_held(&sched_tick));
	mutex_unlock(&sched_tick);
}

struct bpf_sched_link {
	struct bpf_link	link;
	enum bpf_attach_type ea_type;
};

static void bpf_sched_link_release(struct bpf_link *link)
{
	struct bpf_sched_link *sc_link =
		container_of(link, struct bpf_sched_link, link);

	switch (sc_link->ea_type) {
	case BPF_SCHEDULER_TICK:
		sched_tick_detach(link->prog);
		break;
	default:
		break;
	};

}

static void bpf_sched_link_dealloc(struct bpf_link *link)
{
	struct bpf_sched_link *sc_link =
		container_of(link, struct bpf_sched_link, link);

	kfree(sc_link);
}

static const struct bpf_link_ops bpf_sched_link_ops = {
	.release = bpf_sched_link_release,
	.dealloc = bpf_sched_link_dealloc,
};

int scheduler_bpf_link_attach(const union bpf_attr *attr, struct bpf_prog *prog)
{
	struct bpf_link_primer link_primer;
	struct bpf_sched_link *sc_link;
	enum bpf_attach_type ea_type;
	int err;

	if (attr->link_create.flags)
		return -EINVAL;
	if (prog->expected_attach_type != attr->link_create.attach_type)
		return -EINVAL;
	ea_type = prog->expected_attach_type;

	switch (ea_type) {
	case BPF_SCHEDULER_TICK:
		break;
	default:
		return -EINVAL;
	};

	sc_link = kzalloc(sizeof(*sc_link), GFP_USER);
	if (!sc_link)
		return -ENOMEM;
	bpf_link_init(&sc_link->link, BPF_LINK_TYPE_UNSPEC,
		      &bpf_sched_link_ops, prog);
	sc_link->ea_type = ea_type;

	err = bpf_link_prime(&sc_link->link, &link_primer);
	if (err) {
		kfree(sc_link);
		return -EINVAL;
	}

	switch (ea_type) {
	case BPF_SCHEDULER_TICK:
		err = sched_tick_attach(prog);
		break;
	default:
		pr_warn("bad sched bpf ea_type %d, should be unreachable",
			ea_type);
		err = -EINVAL;
		break;
	};
	if (err) {
		bpf_link_cleanup(&link_primer);
		return err;
	}

	return bpf_link_settle(&link_primer);
}

/* netns does this to have a packed array of progs[type].  might do this for the
 * task type only, or maybe for all sched types.
 */
enum sched_bpf_attach_type {
	SCHED_BPF_INVALID = -1,
	SCHED_BPF_TICK = 0,
	MAX_SCHED_BPF_ATTACH_TYPE
};

static inline enum sched_bpf_attach_type
to_sched_bpf_attach_type(enum bpf_attach_type attach_type)
{
	switch (attach_type) {
	case BPF_SCHEDULER_TICK:
		return SCHED_BPF_TICK;
	default:
		return SCHED_BPF_INVALID;
	}
}

int scheduler_bpf_prog_attach(const union bpf_attr *attr, struct bpf_prog *prog)
{
	enum sched_bpf_attach_type type;

	if (attr->target_fd || attr->attach_flags || attr->replace_bpf_fd)
		return -EINVAL;
	type = to_sched_bpf_attach_type(attr->attach_type);
	if (type < 0)
		return -EINVAL;

	/* no task attachable types yet */

	return -1;
}

int scheduler_bpf_prog_detach(const union bpf_attr *attr,
			      enum bpf_prog_type ptype)
{
	struct bpf_prog *prog;
	enum sched_bpf_attach_type type;

	if (attr->attach_flags)
		return -EINVAL;

	type = to_sched_bpf_attach_type(attr->attach_type);
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
scheduler_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	switch (func_id) {
	default:
		return bpf_base_func_proto(func_id);
	}
}

static bool scheduler_is_valid_access(int off, int size,
				      enum bpf_access_type type,
				      const struct bpf_prog *prog,
				      struct bpf_insn_access_aux *info)
{
	/* The verifier guarantees that size > 0. */
	if (off < 0 || off + size > sizeof(struct bpf_scheduler) || off % size)
		return false;

	switch (off) {
	default:
		return false;
	}
}

#define SCHEDULER_ACCESS_FIELD(T, F)					\
	T(BPF_FIELD_SIZEOF(struct bpf_scheduler_kern, F),		\
	  si->dst_reg, si->src_reg,					\
	  offsetof(struct bpf_scheduler_kern, F))

static u32 scheduler_convert_ctx_access(enum bpf_access_type type,
					const struct bpf_insn *si,
					struct bpf_insn *insn_buf,
					struct bpf_prog *prog, u32 *target_size)
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

const struct bpf_verifier_ops scheduler_verifier_ops = {
	.get_func_proto		= scheduler_func_proto,
	.is_valid_access	= scheduler_is_valid_access,
	.convert_ctx_access	= scheduler_convert_ctx_access,
};

const struct bpf_prog_ops scheduler_prog_ops = {
};
