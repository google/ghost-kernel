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

#include <linux/fs.h>
#include <linux/sysfs.h>
#include <linux/kernfs.h>
#include <linux/mm.h>
#include <linux/seq_buf.h>
#include <linux/seq_file.h>

#include "../../fs/kernfs/kernfs-internal.h"

/* Helper for when you "echo foo > ctl" without the -n. */
static void strip_slash_n(char *buf, size_t count)
{
	char *n = strnchr(buf, count, '\n');

	if (n)
		*n = '\0';
}

static struct kernfs_root *ghost_kfs_root;

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

	kref_get(&e->kref);
	return 0;
}

/* For enclave files whose priv directly points to a ghost enclave. */
static void gf_e_release(struct kernfs_open_file *of)
{
	struct ghost_enclave *e = of_to_e(of);

	kref_put(&e->kref, enclave_release);
}

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

/* Called from the scheduler when it destroys the enclave. */
void ghostfs_remove_enclave(struct ghost_enclave *e)
{
	kernfs_remove(e->enclave_dir);
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

	swr_kn = kernfs_create_file(dir, name, 0440, 0, &gf_ops_e_swr, e);
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

static ssize_t gf_ctl_write(struct kernfs_open_file *of, char *buf,
			    size_t len, loff_t off)
{
	unsigned int arg1, arg2;
	int err;

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
	} else {
		pr_err("%s: bad cmd :%s:", __func__, buf);
		return -EINVAL;
	}

	return len;
}

static long gf_ctl_ioctl(struct kernfs_open_file *of, unsigned int cmd,
			 unsigned long arg)
{
	struct ghost_enclave *e = of_to_e(of);

	switch (cmd) {
	case GHOST_IOC_NULL:
		return 0;
	case GHOST_IOC_SW_GET_INFO:
		return ghost_sw_get_info(e,
				(struct ghost_ioc_sw_get_info __user *)arg);
	case GHOST_IOC_SW_FREE:
		return ghost_sw_free(e, (void __user *)arg);
	}
	return -ENOIOCTLCMD;
}

static struct kernfs_ops gf_ops_e_ctl = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_ctl_show,
	.write			= gf_ctl_write,
	.ioctl			= gf_ctl_ioctl,
};

/*
 * Returns the enclave for f, if f is a ghostfs ctl file.  We could support
 * other file types, but since this is a backdoor into the FS, we only need to
 * support ctl.
 *
 * Successful callers must call ghostfs_put_ctl_enclave(f).
 *
 * The kernfs_ops don't need this helper.  kernfs manages the the refcounts.  We
 * need to do it manually here, because this is is a "backdoor" function to get
 * the enclave pointer.  That pointer is kept alive by kernfs.
 */
struct ghost_enclave *ghostfs_ctl_to_enclave(struct file *f)
{
	struct kernfs_node *kn;

	kn = kernfs_node_from_file(f);
	if (!kn)
		return NULL;
	if (kernfs_type(kn) != KERNFS_FILE)
		return NULL;
	if (kn->attr.ops != &gf_ops_e_ctl)
		return NULL;
	if (!kernfs_get_active(kn))
		return NULL;
	WARN_ON(!kn->priv);
	return kn->priv;
}

/* Pair this with a successful ghostfs_ctl_to_enclave call. */
void ghostfs_put_enclave_ctl(struct file *f)
{
	struct kernfs_node *kn;

	kn = kernfs_node_from_file(f);
	if (WARN_ON(!kn))
		return;
	if (WARN_ON(kernfs_type(kn) != KERNFS_FILE))
		return;
	if (WARN_ON(kn->attr.ops != &gf_ops_e_ctl))
		return;
	kernfs_put_active(kn);
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
	spin_unlock_irqrestore(&e->lock, fl);

	seq_printf(sf, "active %s\n", is_active ? "yes" : "no");
	return 0;
}

static struct kernfs_ops gf_ops_e_status = {
	.open			= gf_e_open,
	.release		= gf_e_release,
	.seq_show		= gf_status_show,
};

static struct gf_dirent enclave_dirtab[] = {
	{
		.name		= "sw_regions",
		.mode		= 0555,
		.is_dir		= true,
	},
	{
		.name		= "agent_online",
		.mode		= 0664,
		.ops		= &gf_ops_e_agent_online,
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
		.name		= "runnable_timeout",
		.mode		= 0664,
		.ops		= &gf_ops_e_runnable_timeout,
	},
	{
		.name		= "status",
		.mode		= 0444,
		.ops		= &gf_ops_e_status,
	},
	{0},
};

/* Caller is responsible for cleanup.  Removing the parent will suffice. */
static int gf_add_files(struct kernfs_node *parent, struct gf_dirent *dirtab,
			struct ghost_enclave *priv)
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

static int make_enclave(struct kernfs_node *parent, unsigned long id)
{
	struct kernfs_node *dir;
	struct ghost_enclave *e;
	char name[31];
	int ret;

	/*
	 * ghost_create_enclave() is mostly just "alloc and initialize".
	 * Anything done by it gets undone in enclave_release, and it is not
	 * discoverable, usable, or otherwise hooked into the kernel until
	 * kernfs_active().
	 */
	e = ghost_create_enclave();
	if (!e)
		return -ENOMEM;
	e->id = id;
	if (snprintf(name, sizeof(name), "enclave_%lu", id) >= sizeof(name)) {
		ret = -ENOSPC;
		goto out_e;
	}

	dir = kernfs_create_dir(parent, name, 0555, NULL);
	if (IS_ERR(dir)) {
		ret = PTR_ERR(dir);
		goto out_e;
	}
	e->enclave_dir = dir;

	ret = gf_add_files(dir, enclave_dirtab, e);
	if (ret)
		goto out_dir;

	/*
	 * Once the enclave has been activated, it is available to userspace and
	 * can be used for scheduling.  After that, we must destroy it by
	 * calling ghost_destroy_enclave(), not by releasing the reference.
	 */
	kernfs_activate(dir);	/* recursive */

	return 0;

out_dir:
	kernfs_remove(dir);	/* recursive */
out_e:
	kref_put(&e->kref, enclave_release);
	return ret;
}

static ssize_t gf_top_ctl_write(struct kernfs_open_file *of, char *buf,
				size_t len, loff_t off)
{
	struct kernfs_node *ctl = of->kn;
	struct kernfs_node *top_dir = ctl->parent;
	unsigned long x;
	int ret;

	strip_slash_n(buf, len);

	/* This will ignore any extra digits or characters beyond the %u. */
	ret = sscanf(buf, "create %lu", &x);
	if (ret == 1) {
		ret = make_enclave(top_dir, x);
		return ret ? ret : len;
	}

	return -EINVAL;
}

static struct kernfs_ops gf_ops_top_ctl = {
	.write			= gf_top_ctl_write,
};

static int gf_top_version_show(struct seq_file *sf, void *v)
{
	seq_printf(sf, "%u", GHOST_VERSION);
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

/*
 * Most gf_dirent file sizes are not known at compile time.  Most don't matter
 * for sysfs and we can leave them as 0.  But for anything that gets mmapped,
 * it's convenient for userspace for the kernel to say how big it is.
 */
static void runtime_adjust_dirtabs(void)
{
	struct gf_dirent *enc_txn;

	enc_txn = gf_find_file(enclave_dirtab, "cpu_data");
	if (WARN_ON(!enc_txn))
		return;
	enc_txn->size = GHOST_CPU_DATA_REGION_SIZE;
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

	runtime_adjust_dirtabs();

	kernfs_activate(ghost_kfs_root->kn);

	return ret;
}

static struct dentry *ghost_mount(struct file_system_type *fs_type,
				  int flags, const char *unused_dev_name,
				  void *data)
{
	struct dentry *dentry;

	/* Technically, this should be in uapi/linux/magic.h. */
	#define GHOST_SUPER_MAGIC 0xBAD1DEA2

	VM_BUG_ON(!ghost_kfs_root);
	dentry = kernfs_mount(fs_type, flags, ghost_kfs_root,
			      GHOST_SUPER_MAGIC, NULL);
	if (IS_ERR(dentry))
		WARN(1, "Failed to mount ghostfs!");
	return dentry;
}

static void ghost_kill_sb(struct super_block *sb)
{
	kernfs_kill_sb(sb);
}

static struct file_system_type ghost_fs_type = {
	.name    = "ghost",
	.mount   = ghost_mount,
	.kill_sb = ghost_kill_sb,
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
