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
#ifndef _KERNEL_SCHED_GHOST_H_
#define _KERNEL_SCHED_GHOST_H_

#ifndef __INCLUDE_KERNEL_SCHED_GHOST
#error "ghost.h can only be included from ghost.c or ghostfs.c"
#endif

struct ghost_sw_region {
	struct list_head list;			/* ghost_enclave glue */
	uint32_t alloc_scan_start;		/* allocator starts scan here */
	struct ghost_sw_region_header *header;  /* pointer to vmalloc memory */
	size_t mmap_sz;				/* size of mmapped region */
	struct ghost_enclave *enclave;
};

/* In kernel/sched/ghostfs.c */
struct ghost_enclave *ghostfs_ctl_to_enclave(struct file *f);
void ghostfs_put_enclave_ctl(struct file *f);
void ghostfs_remove_enclave(struct ghost_enclave *e);

/* In kernel/sched/ghost.c */
struct ghost_enclave *ghost_create_enclave(void);
void ghost_destroy_enclave(struct ghost_enclave *e);
int ghost_enclave_set_cpus(struct ghost_enclave *e, const struct cpumask *cpus);
int ghost_region_mmap(struct file *file, struct vm_area_struct *vma,
		      void *addr, ulong mapsize);
int ghost_cpu_data_mmap(struct file *file, struct vm_area_struct *vma,
			struct ghost_cpu_data **cpu_data, ulong mapsize);
struct ghost_sw_region *ghost_create_sw_region(struct ghost_enclave *e,
					       unsigned int id,
					       unsigned int node);

int ghost_sw_get_info(struct ghost_enclave *e,
		      struct ghost_ioc_sw_get_info __user *arg);
int ghost_sw_free(struct ghost_enclave *e, struct ghost_sw_info __user *uinfo);
int ghost_create_queue(struct ghost_enclave *e,
		       struct ghost_ioc_create_queue __user *arg);
int ghost_associate_queue(struct ghost_ioc_assoc_queue __user *arg);
int ghost_set_default_queue(struct ghost_enclave *e,
			    struct ghost_ioc_set_default_queue __user *arg);
int ghost_config_queue_wakeup(struct ghost_ioc_config_queue_wakeup __user *arg);
int ghost_get_cpu_time(struct ghost_ioc_get_cpu_time __user *arg);
int ioctl_ghost_commit_txn(struct ghost_enclave *e,
			   struct ghost_ioc_commit_txn __user *arg);
int ghost_sync_group(struct ghost_enclave *e,
		     struct ghost_ioc_commit_txn __user *arg);
int ghost_timerfd_settime(struct ghost_ioc_timerfd_settime __user *arg);

/* Stub functions for open source ghOSt code. */

/* These functions should not be open sourced. */
static inline void kvm_register_core_conflict(int cpu) {}
static inline bool try_ipiless_wakeup(int cpu) { return false; }

#endif	/* _KERNEL_SCHED_GHOST_H_ */
