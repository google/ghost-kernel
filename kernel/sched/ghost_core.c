#include <linux/kernfs.h>

#include "sched.h"

static struct kernfs_root *ghost_kfs_root;

extern const struct ghost_abi __begin_ghost_abi[];
extern const struct ghost_abi __end_ghost_abi[];

#define first_ghost_abi	    (&__begin_ghost_abi[0])
#define	last_ghost_abi	    (&__end_ghost_abi[-1])

#define for_each_abi(abi) \
	for (abi = first_ghost_abi; abi <= last_ghost_abi; abi++)

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
