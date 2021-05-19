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

#include <linux/types.h>

/* These functions should not be open sourced. */
static inline void kvm_register_core_conflict(int cpu) {}
static inline bool try_ipiless_wakeup(int cpu) { return false; }
// Have `bpf_sched_ghost_skip_tick` return true for now until we integrate eBPF
static inline bool bpf_sched_ghost_skip_tick(void) { return true; }

/* These functions/types are available in newer versions of Linux. */
typedef long long __kernel_time64_t;

struct __kernel_timespec {
        __kernel_time64_t       tv_sec;                 /* seconds */
        long long               tv_nsec;                /* nanoseconds */
};

struct __kernel_itimerspec {
        struct __kernel_timespec it_interval;    /* timer period */
        struct __kernel_timespec it_value;       /* timer expiration */
};

static inline int get_timespec64_ghost(struct timespec64 *ts,
				       const struct __kernel_timespec __user *uts)
{
	struct __kernel_timespec kts;
	int ret;

	ret = copy_from_user(&kts, uts, sizeof(kts));
	if (ret)
		return -EFAULT;

	ts->tv_sec = kts.tv_sec;

	/* Zero out the padding in compat mode */
	if (in_compat_syscall())
		kts.tv_nsec &= 0xFFFFFFFFUL;

	/* In 32-bit mode, this drops the padding */
	ts->tv_nsec = kts.tv_nsec;

	return 0;
}

static inline int put_timespec64_ghost(const struct timespec64 *ts,
				       struct __kernel_timespec __user *uts)
{
	struct __kernel_timespec kts = {
		.tv_sec = ts->tv_sec,
		.tv_nsec = ts->tv_nsec
	};

	return copy_to_user(uts, &kts, sizeof(kts)) ? -EFAULT : 0;
}

static inline int get_itimerspec64_ghost(struct itimerspec64 *it,
					 const struct __kernel_itimerspec __user *uit)
{
	int ret;

	ret = get_timespec64_ghost(&it->it_interval, &uit->it_interval);
	if (ret)
		return ret;

	ret = get_timespec64_ghost(&it->it_value, &uit->it_value);

	return ret;
}

static inline int put_itimerspec64_ghost(const struct itimerspec64 *it,
					 struct __kernel_itimerspec __user *uit)
{
	int ret;

	ret = put_timespec64_ghost(&it->it_interval, &uit->it_interval);
	if (ret)
		return ret;

	ret = put_timespec64_ghost(&it->it_value, &uit->it_value);

	return ret;
}
