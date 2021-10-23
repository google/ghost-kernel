# ghOSt: Fast &amp; Flexible User-Space Delegation of Linux Scheduling

ghOSt is a general-purpose delegation of scheduling policy implemented on top of
the Linux kernel. The ghOSt framework provides a rich API that receives
scheduling decisions for processes from userspace and actuates them as
transactions. Programmers can use any language or tools to develop policies,
which can be upgraded without a machine reboot. ghOSt supports policies for a
range of scheduling objectives, from µs-scale latency, to throughput, to energy
efficiency, and beyond, and incurs low overheads for scheduling actions. Many
policies are just a few hundred lines of code. Overall, ghOSt provides a
performant framework for delegation of thread scheduling policy to userspace
processes that enables policy optimization, non-disruptive upgrades, and fault
isolation.

[SOSP '21 Paper](https://dl.acm.org/doi/10.1145/3477132.3483542)\
[SOSP '21 Talk](https://youtu.be/j4ABe4dsbIY)

You must compile and install this kernel in order to use the [ghOSt userspace
component](https://www.github.com/google/ghost-userspace).

This kernel is Linux 5.11. We recommend installing Ubuntu 20.04 LTS, which ships
with Linux 5.4 by default, as the distribution. Compile this kernel on Ubuntu
20.04 and then replace the existing 5.4 kernel with this one.

This is not an officially supported Google product.
