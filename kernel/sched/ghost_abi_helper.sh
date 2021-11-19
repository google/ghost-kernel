#!/bin/bash

progname=`basename $0`

err_exit() {
	local msg=$1
	echo "*** ${msg}" 1>&2
	exit 1
}

usage() {
  local rc=$1
  echo "Usage: $progname [-hs][-d <abi>]"
  echo "   -h: print this help message"
  echo "   -s: snapshot abi (implicit if no other option is specified)"
  echo "   -d: delete snapshot at the specified version"
  exit $rc
}

check_topdir() {
	local topdir=$1

	if [ -d ${topdir}/kernel/sched			-a \
	     -f ${topdir}/kernel/sched/ghost.c		-a \
	     -f ${topdir}/kernel/sched/ghost.h		-a \
	     -f ${topdir}/include/uapi/linux/ghost.h ]; then
		return 0
	else
		return -1
	fi
}

delete_snapshot=0
abi=0

while getopts "hsd:" opt; do
  case $opt in
    d)
      abi="${OPTARG}"
      delete_snapshot=1
      ;;
    s)
      delete_snapshot=0
      ;;
    h)
      usage 0
      ;;
    \?)
      echo "Invalid option: -$OPTARG" >&2
      ;;
  esac
done

shift "$((OPTIND - 1))"

if [ $# -gt 0 ]; then
        usage 1
fi

topdir=${PWD}
check_topdir ${topdir} || err_exit "Are you in the top level kernel directory?"

sched_dir=${topdir}/kernel/sched
uapi_dir=${topdir}/include/uapi/linux

if [ $delete_snapshot -eq 0 ]; then
	abi=`grep GHOST_VERSION ${uapi_dir}/ghost.h | awk '{print $3}'`
	if [ $? -ne 0 -o -z "${abi}" ]; then
		err_exit "unable to parse GHOST_VERSION from ghost.h"
	fi
fi

snapshot_dir=${sched_dir}/ghost_abi_${abi}

if [ ${delete_snapshot} -eq 1 ]; then
	git rm -r ${snapshot_dir} || err_exit "error git rm'ing ${snapshot_dir}"
	sed -i "/ghost_abi_${abi}/d" ${sched_dir}/Makefile || \
		err_exit "error removing ghost_abi_${abi} from Makefile"
	rm -rf ${snapshot_dir}
	git commit -a -m "sched: delete snapshot of ghost abi ${abi}"
	exit $?
fi

# Take a snapshot of the ABI.
mkdir ${snapshot_dir} || err_exit "error creating ${snapshot_dir}"
cp ${sched_dir}/ghost.h ${snapshot_dir} || err_exit "error creating ghost.h"
cp ${sched_dir}/ghost.c ${snapshot_dir} || err_exit "error creating ghost.c"
cp ${uapi_dir}/ghost.h ${snapshot_dir}/ghost_uapi.h || err_exit "error creating ghost_uapi.h"

cat > ${snapshot_dir}/Makefile << EOF
obj-\$(CONFIG_SCHED_CLASS_GHOST) += ghost.o
CFLAGS_ghost.o += -I\$(srctree)/fs/kernfs -I\$(srctree)/kernel/sched
EOF

cat >> ${sched_dir}/Makefile << EOF
obj-\$(CONFIG_SCHED_CLASS_GHOST) += ghost_abi_${abi}/
EOF

sed -i -e "s/^#define\s\+GHOST_VERSION\s\+[0-9]\+$/#define GHOST_VERSION $((abi+1))/" \
    ${uapi_dir}/ghost.h || err_exit "error bumping current abi version"

git add ${snapshot_dir} ${sched_dir}/Makefile ${uapi_dir}/ghost.h || \
	err_exit "git add"

git commit -m "sched: snapshot ghost abi ${abi}"
exit $?
