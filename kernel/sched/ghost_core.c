#include <linux/kernfs.h>

#define _GHOST_MAYBE_CONST
#include "sched.h"

static struct kernfs_root *ghost_kfs_root;

extern const struct ghost_abi __begin_ghost_abi[];
extern const struct ghost_abi __end_ghost_abi[];

#define first_ghost_abi	    (&__begin_ghost_abi[0])
#define	last_ghost_abi	    (&__end_ghost_abi[-1])

#define for_each_abi(abi) \
	for (abi = first_ghost_abi; abi <= last_ghost_abi; abi++)

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

static ghost_abi_ptr_t ghost_abi_lookup(uint version)
{
	ghost_abi_ptr_t abi;

	for_each_abi(abi) {
		if (abi->version == version)
			return abi;
	}

	return NULL;
}

static int make_enclave(struct kernfs_node *parent, unsigned long id,
			unsigned int version)
{
	struct kernfs_node *dir;
	struct ghost_enclave *e;
	ghost_abi_ptr_t abi;
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
	e = abi->create_enclave(abi, dir, id);
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
	int ret;

	gf_strip_slash_n(buf, len);

	/* This will ignore any extra digits or characters beyond the %u. */
	ret = sscanf(buf, "create %lu %u", &x, &abi_num);
	if (ret == 2) {
		ret = make_enclave(top_dir, x, abi_num);
		return ret ? ret : len;
	}

	return -EINVAL;
}

static struct kernfs_ops gf_ops_top_ctl = {
	.write			= gf_top_ctl_write,
};

static int gf_top_version_show(struct seq_file *sf, void *v)
{
	ghost_abi_ptr_t abi;

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
	ghost_abi_ptr_t abi;
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
		WARN(1, "Failed to mount ghostfs!");
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

/* per_cpu(cpu_owner) protected by 'cpu_rsvp' */
static DEFINE_SPINLOCK(cpu_rsvp);
static DEFINE_PER_CPU_READ_MOSTLY(struct ghost_enclave *, cpu_owner);

DEFINE_PER_CPU_READ_MOSTLY(struct ghost_enclave *, enclave);

int ghost_claim_cpus(struct ghost_enclave *e, const struct cpumask *new_cpus)
{
	int cpu;

	/*
	 * 'e->lock' must be held across ghost_claim_cpus() and the
	 * corresponding ghost_publish_cpu().
	 */
	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);

	for_each_cpu(cpu, new_cpus) {
		/*
		 * Let's make sure that 'cpu' hasn't been already claimed by
		 * another enclave.
		 */
		if (per_cpu(cpu_owner, cpu)) {
			spin_unlock(&cpu_rsvp);
			return -EBUSY;
		}
		WARN_ON_ONCE(per_cpu(enclave, cpu) != NULL);
	}

	for_each_cpu(cpu, new_cpus)
		per_cpu(cpu_owner, cpu) = e;

	spin_unlock(&cpu_rsvp);
	return 0;
}

void ghost_publish_cpu(struct ghost_enclave *e, int cpu)
{
	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);
	WARN_ON_ONCE(per_cpu(cpu_owner, cpu) != e);
	WARN_ON_ONCE(per_cpu(enclave, cpu) != NULL);
	rcu_assign_pointer(per_cpu(enclave, cpu), e);
	spin_unlock(&cpu_rsvp);
}

void ghost_unpublish_cpu(struct ghost_enclave *e, int cpu)
{
	/*
	 * 'e->lock' must be held across ghost_unpublish_cpu() and the
	 * corresponding ghost_return_cpu().
	 */
	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);
	WARN_ON_ONCE(per_cpu(cpu_owner, cpu) != e);
	WARN_ON_ONCE(per_cpu(enclave, cpu) != e);
	rcu_assign_pointer(per_cpu(enclave, cpu), NULL);
	spin_unlock(&cpu_rsvp);
}

void ghost_return_cpu(struct ghost_enclave *e, int cpu)
{
	VM_BUG_ON(!spin_is_locked(&e->lock));

	spin_lock(&cpu_rsvp);
	WARN_ON_ONCE(per_cpu(cpu_owner, cpu) != e);
	WARN_ON_ONCE(per_cpu(enclave, cpu) != NULL);
	per_cpu(cpu_owner, cpu) = NULL;
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

void ghost_pnt_prologue(struct rq *rq, struct task_struct *prev)
{
	struct ghost_enclave *e;

	VM_BUG_ON(preemptible());
	VM_BUG_ON(rq != this_rq());

	/* rcu_read_lock_sched() not needed; preemption is disabled. */
	e = rcu_dereference_sched(per_cpu(enclave, cpu_of(rq)));

	if (e != NULL)
		e->abi->pnt_prologue(rq, prev);
}

void __init init_sched_ghost_class(void)
{
	int64_t cpu;

	for_each_possible_cpu(cpu)
		per_cpu(sync_group_cookie, cpu) = cpu << SG_COOKIE_CPU_SHIFT;
}

/*
 * Helper to get an fd and translate it to an enclave.  Ghostfs will maintain a
 * kref on the enclave.  That kref is increffed when the file was opened, and
 * that kref is maintained by this call (a combination of fdget and
 * kernfs_get_active).  Once you call ghost_fdput_enclave(), the enclave kref
 * can be released.
 *
 * Returns NULL if there is not a ghost_enclave for this FD, which could be due
 * to concurrent enclave destruction.
 *
 * Caller must call ghost_fdput_enclave with e and &fd_to_put, even on error.
 */
struct ghost_enclave *ghost_fdget_enclave(int fd, struct fd *fd_to_put)
{
	ghost_abi_ptr_t abi;
	struct ghost_enclave *e = NULL;

	*fd_to_put = fdget(fd);
	if (!fd_to_put->file)
		return NULL;

	for_each_abi(abi) {
		e = abi->ctlfd_enclave_get(fd_to_put->file);
		if (e)
			break;
	}
	return e;
}

/*
 * Pairs with calls to ghost_fdget_enclave().  You can't call this while holding
 * the rq lock.
 */
void ghost_fdput_enclave(struct ghost_enclave *e, struct fd *fd)
{
	if (e)
		e->abi->ctlfd_enclave_put(fd->file);
	fdput(*fd);
}

#define GHOST_SCHED_TASK_PRIO	0
#define GHOST_SCHED_AGENT_PRIO	1
int ghost_validate_sched_attr(const struct sched_attr *attr)
{
	/*
	 * A thread can only make a task an agent if the thread has the
         * CAP_SYS_NICE capability.
	 */
	switch (attr->sched_priority) {
		case GHOST_SCHED_TASK_PRIO:
			return 0;
		case GHOST_SCHED_AGENT_PRIO:
			return capable(CAP_SYS_NICE) ? 0 : -EPERM;
		default:
			return -EINVAL;
	}
}

bool ghost_agent(const struct sched_attr *attr)
{
	return attr->sched_priority == GHOST_SCHED_AGENT_PRIO;
}

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
	BUILD_BUG_ON(BPF_FUNC_ghost_wake_agent != 204);

	/* rcu_read_lock_sched() not needed; preemption is disabled. */
	e = rcu_dereference_sched(per_cpu(enclave, smp_processor_id()));

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
	BUILD_BUG_ON(BPF_FUNC_ghost_run_gtid != 205);

	/* rcu_read_lock_sched() not needed; preemption is disabled. */
	e = rcu_dereference_sched(per_cpu(enclave, smp_processor_id()));

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

static const struct bpf_func_proto *
ghost_sched_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	int eat = bpf_prog_eat_type(prog);

	switch (func_id) {
	case BPF_FUNC_ghost_wake_agent:
		return &bpf_ghost_wake_agent_proto;
	case BPF_FUNC_ghost_run_gtid:
		switch (eat) {
		case BPF_GHOST_SCHED_PNT:
			return &bpf_ghost_run_gtid_proto;
		default:
			return NULL;
		}
	default:
		return bpf_base_func_proto(func_id);
	}
}

static bool ghost_sched_is_valid_access(int off, int size,
					enum bpf_access_type type,
					const struct bpf_prog *prog,
					struct bpf_insn_access_aux *info)
{
	/* struct bpf_ghost_sched is empty so all accesses are invalid. */
	return false;
}


const struct bpf_verifier_ops ghost_sched_verifier_ops = {
	.get_func_proto		= ghost_sched_func_proto,
	.is_valid_access	= ghost_sched_is_valid_access,
};

const struct bpf_prog_ops ghost_sched_prog_ops = {};

static const struct bpf_func_proto *
ghost_msg_func_proto(enum bpf_func_id func_id, const struct bpf_prog *prog)
{
	switch (func_id) {
	case BPF_FUNC_ghost_wake_agent:
		return &bpf_ghost_wake_agent_proto;
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
	ghost_abi_ptr_t abi = ghost_abi_lookup(version);

	if (WARN_ON_ONCE(!abi))
		return false;

	return abi->ghost_msg_is_valid_access(off, size, type, prog, info);
}

const struct bpf_verifier_ops ghost_msg_verifier_ops = {
	.get_func_proto		= ghost_msg_func_proto,
	.is_valid_access	= ghost_msg_is_valid_access,
};

const struct bpf_prog_ops ghost_msg_prog_ops = {};

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

	e->abi->bpf_link_detach(e, link->prog,
				sc_link->prog_type, sc_link->ea_type);

	kref_put(&e->kref, e->abi->enclave_release);
	sc_link->e = NULL;
}

static const struct bpf_link_ops bpf_ghost_link_ops = {
	.release = bpf_ghost_link_release,
	.dealloc = bpf_ghost_link_dealloc,
};

int ghost_bpf_link_attach(const union bpf_attr *attr,
			  struct bpf_prog *prog)
{
	struct bpf_link_primer link_primer;
	struct bpf_ghost_link *sc_link;
	enum bpf_attach_type ea_type;
	struct ghost_enclave *e;
	struct fd f_enc = {0};
	int err, ea_abi;

	if (attr->link_create.flags)
		return -EINVAL;
	if (prog->expected_attach_type != attr->link_create.attach_type)
		return -EINVAL;

	/* Mask the ABI value encoded in the upper 16 bits. */
	ea_type = bpf_prog_eat_type(prog);
	ea_abi = bpf_prog_eat_abi(prog);

	switch (prog->type) {
	case BPF_PROG_TYPE_GHOST_SCHED:
		switch (ea_type) {
		case BPF_GHOST_SCHED_SKIP_TICK:
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

	e = ghost_fdget_enclave(attr->link_create.target_fd, &f_enc);
	if (!e || ea_abi != enclave_abi(e)) {
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

	err = e->abi->bpf_link_attach(e, prog, prog->type, ea_type);

	if (err) {
		/* bpf_link_cleanup() triggers .dealloc, but not .release. */
		bpf_link_cleanup(&link_primer);
		kref_put(&e->kref, e->abi->enclave_release);
		return err;
	}

	return bpf_link_settle(&link_primer);
}
#endif
