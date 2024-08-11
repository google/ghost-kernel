# ghOSt

# Introduction to ghOSt

ghOSt is a general-purpose delegation of scheduling policy implemented on top of the Linux kernel. The ghOSt framework provides a rich API that receives scheduling decisions for processes from userspace and actuates them as transactions. Programmers can use any language or tools to develop policies, which can be upgraded without a machine reboot. ghOSt supports policies for a range of scheduling objectives, from µs-scale latency, to throughput, to energy efficiency, and beyond, and incurs low overheads for scheduling actions. Many policies are just a few hundred lines of code. Overall, ghOSt provides a performant framework for delegation of thread scheduling policy to userspace processes that enables policy optimization, non-disruptive upgrades, and fault isolation.

[SOSP’21 Paper](https://dl.acm.org/doi/10.1145/3477132.3483542)

[SOSP’21 Talk](https://www.youtube.com/watch?v=j4ABe4dsbIY)

# Setting up the ghOSt kernel

## Checking for software requirements (Minimal)

| Program | Minimal version | Command to check the version |
| --- | --- | --- |
| GNU C | 4.9 | gcc --version |
| Clang/LLVM (optional) | 10.0.1 | clang --version |
| GNU make | 3.81 | make --version |
| binutils | 2.23 | ld -v |
| flex | 2.5.35 | flex --version |
| bison | 2.0 | bison --version |
| util-linux | 2.10o | fdformat --version |
| kmod | 13 | depmod -V |
| e2fsprogs | 1.41.4 | e2fsck -V |
| jfsutils | 1.1.3 | fsck.jfs -V |
| reiserfsprogs | 3.6.3 | reiserfsck -V |
| xfsprogs | 2.6.0 | xfs_db -V |
| squashfs-tools | 4.0 | mksquashfs -version |
| btrfs-progs | 0.18 | btrfsck |
| pcmciautils | 004 | pccardctl -V |
| quota-tools | 3.09 | quota -V |
| PPP | 2.4.0 | pppd --version |
| nfs-utils | 1.0.5 | showmount --version |
| procps | 3.2.0 | ps --version |
| oprofile | 0.9 | operf --version |
| udev | 081 | udevadm --version |
| grub | 0.93 | grub --version || grub-install --version |
| mcelog | 0.6 | mcelog --version |
| iptables | 1.4.2 | iptables -V |
| openssl & libcrypto | 1.0.0 | openssl version |
| bc | 1.06.95 | bc --version |
| Sphinx | 1.3 | sphinx-build --version |

***NOTE:** 

**Sphinx**

This package is needed only to build the Kernel documentation

To install this package:

```
sudo apt-get install python3-sphinx
```

**operf**

If you run into an error such as “`Unexpected error running operf: Permission denied`” try the following:

```
cd /proc/sys/kernel/
sudo gedit perf_event_paranoid
```

change the value to 2 in the file, save and close it.

While checking the operf version, if you run into the following “Your kernel's Performance Events Subsystem does not support your processor type.”, you can simply ignore it and continue.

**mcelog**

To download the mcelog package:

```
git clone git://git.kernel.org/pub/scm/utils/cpu/mce/mcelog.git
cd mcelog/
make
sudo make install
```

**libelf-dev**

Install the libelf-dev package using the following command:

```
sudo apt-get install libelf-dev
```

**libssl-dev**

Install the libssl-dev package using the following command:

```
sudo apt-get install libssl-dev
```

**zstd**

Install the zstd package using the following command:

```
sudo apt install zstd
```

to verify one last time if all the necessary packages/libraries are installed, run the following command:

```
sudo apt-get install build-essential linux-source bc kmod cpio flex libncurses5-dev libelf-dev libssl-dev dwarves bison
```

## Installing the Kernel

Now that we have the minimum software requirements satisfied, we will move on to building the Linux ghOSt kernel.

clone the ghOSt kernel repository:

```
git clone https://github.com/google/ghost-kernel

#Note that the repository has gone through several updates and changes over the years,
#hence the repository might be a very huge download. If you wish to create a shallow 
#clone with a history truncated to the specified number of commits,
#use the --depth parameter while cloning the repository.
#to know more about the various parameters of git clone refer the documentation:
#[https://git-scm.com/docs/git-clone](https://git-scm.com/docs/git-clone)

git clone --depth 1 https://github.com/google/ghost-kernel
```

## Building the Kernel

When compiling the kernel, all output files will per default be stored together with the kernel source code. Using the option `make O=output/dir` allows you to specify an alternate place for the output files (including .config).

To configure and build the kernel, head into the cloned repository folder and use:

```
make O=/home/name/build/kernel menuconfig
#just save and exit the menuconfig

# 'n' implies the number of cores you can assign to execute the *make* command parallelly.
make -j n O=/home/name/build/kernel
sudo make -j n O=/home/name/build/kernel modules_install install
make -j n oldconfig
make bindeb-pkg -j n
```

***NOTE:**

You may run into a “`*** No rule to make target 'debian/certs/debian-uefi-certs.pem', needed by 'certs/x509_certificate_list'`” error while executing the make command.

To resolve this issue:

```
#open the .config file in the ghost-kernel directory and make sure the following
#is reflected:

#
# Certificates for signature checking
#
CONFIG_MODULE_SIG_KEY="certs/signing_key.pem"
CONFIG_MODULE_SIG_KEY_TYPE_RSA=y
CONFIG_MODULE_SIG_KEY_TYPE_ECDSA=y
CONFIG_SYSTEM_TRUSTED_KEYRING=y
CONFIG_SYSTEM_TRUSTED_KEYS="/usr/local/src/debian/canonical-certs.pem"
CONFIG_SYSTEM_EXTRA_CERTIFICATE=y
CONFIG_SYSTEM_EXTRA_CERTIFICATE_SIZE=4096
CONFIG_SECONDARY_TRUSTED_KEYRING=y
CONFIG_SYSTEM_BLACKLIST_KEYRING=y
CONFIG_SYSTEM_BLACKLIST_HASH_LIST=""
CONFIG_SYSTEM_REVOCATION_LIST=y
CONFIG_SYSTEM_REVOCATION_KEYS="/usr/local/src/debian/canonical-revoked-certs.pem"
```

# Setting up the ghOSt userspace

## Compilation

The ghOSt userspace can be compiled in Ubuntu 20.04 or newer.

1. Clone the ghOSt userspace repository.

```
git clone https://github.com/google/ghost-userspace
```

1. We use the Google Bazel build system to compile the userspace components of ghOSt. Preferably install using Bazelisk. 
2. Follow the steps to download Bazel:
    1. Go to [https://github.com/bazelbuild/bazelisk/releases](https://github.com/bazelbuild/bazelisk/releases)
    2. Download the specific release you want on your system and install the package.
    3. Or follow the steps given below

```
#insert the version number in the blank
wget -c https://github.com/bazelbuild/bazelisk/releases/download/vx.x.x/bazelisk-linux-amd64

#The following commands are with respect to the release downloaded in our system.
#Please change the directory names etc. where ever required.
chmod +x bazelisk-linux-amd64
sudo mv bazelisk-linux-amd64 /usr/local/bin/bazel

#To verify your Bazel installation, run:
bazel version

```

1. Install ghOSt dependencies:

```
sudo apt update
sudo apt install libnuma-dev libcap-dev libelf-dev libbfd-dev gcc clang-12 llvm zlib1g-dev python-is-python3
```

Note that ghOSt requires GCC 9 or newer and Clang 12 or newer.

Ensure you have python2 installed on your system.

1. Compile and run the ghOSt userspace component from the root directory

```
bazel build -c opt ...
```

`-c opt` tells Bazel to build the targets with optimizations turned on. `...` tells Bazel to build all targets in the `BUILD` file and all `BUILD` files in subdirectories, including the core ghOSt library, the eBPF code, the schedulers, the unit tests, the experiments, and the scripts to run the experiments, along with all of the dependencies for those targets. If you prefer to build individual targets rather than all of them to save compile time, replace `...` with an individual target name, such as `fifo_per_cpu_agent`.

1. Running the ghOSt tests:
    
    To run a test, launch the test binary directly:
    
    ```
    sudo bazel-bin/fifo_per_cpu_agent
    ```
    
    Generally, Bazel encourages the use of `bazel test` when running tests. However, `bazel test` sandboxes the tests so that they have read-only access to `/sys` and are constrained in how long they can run for. However, the tests need write access to `/sys/fs/ghost` to coordinate with the kernel and may take a long time to complete. Thus, to avoid sandboxing, launch the test binaries directly (e.g., `bazel-bin/fifo_per_cpu_agent`).
    
2. Running a ghOSt scheduler
    
    We will run the per-CPU FIFO ghOSt scheduler and use it to schedule Linux pthreads.
    
    1. Build the per-CPU FIFO scheduler:
        
        ```
        bazel build -c opt fifo_per_cpu_agent
        ```
        
    2. Build `simple_exp`, which launches a series of pthreads that run in ghOSt. `simple_exp` is a collection of tests.
        
        ```
        bazel build -c opt simple_exp
        ```
        
    3. Launch the per-CPU FIFO ghOSt scheduler:
        
        ```
        sudo bazel-bin/fifo_per_cpu_agent --ghost_cpus 0-1
        ```
        
        The scheduler launches ghOSt agents on CPUs (i.e., logical cores) 0 and 1 and will therefore schedule ghOSt tasks onto CPUs 0 and 1. Adjust the `--ghost_cpus` command line argument value as necessary. For example, if you have an 8-core machine and you wish to schedule ghOSt tasks on all cores, then pass `0-7` to `--ghost_cpus`.
        
    4. Launch `simple_exp`:
        
        ```
        bazel-bin/simple_exp
        ```
        
        `simple_exp` will launch pthreads. These pthreads in turn will move themselves into the ghOSt scheduling class and thus will be scheduled by the ghOSt scheduler. When `simple_exp` has finished running all tests, it will exit.
        
    5. Use `Ctrl-C` to send a `SIGINT` signal to `fifo_per_cpu_agent` to get it to stop.

***NOTE**

If you encounter errors, try to do `bazel clean`.

If you encounter an `Error: failed to load BTF from /sys/kernel/btf/vmlinux: Invalid argument` error, execute `ls /lib/modules/5.11.0+/` verify that you have the headers directory in it. If not execute the following commands:

```
make headers_install INSTALL_HDR_PATH=/usr
sudo make headers_install INSTALL_HDR_PATH=/usr
ls /usr/include #on executing this, you should see all your header files.
```

Try compiling the userspace again.

# References

[https://github.com/google/ghost-kernel](https://github.com/google/ghost-kernel)

[https://github.com/google/ghost-userspace](https://github.com/google/ghost-userspace)

[https://github.com/bazelbuild/bazelisk/releases](https://github.com/bazelbuild/bazelisk/releases)