0. Pre-request:
    1. [Odroid n2 board](https://www.hardkernel.com/shop/odroid-n2-with-4gbyte-ram/) (n2+ should be fine, but I have not test it yet).
    2. [Armbian linux image](https://www.armbian.com/odroid-n2/): the version of image I'm using is `Armbian_22.02.2_Odroidn2_focal_current_5.10.103`.
1. Install required packages
`
    $sudo apt-get install git fakeroot build-essential ncurses-dev xz-utils libssl-dev bc flex libelf-dev bison -y
`
2. Clone the source code
`$ git clone https://github.com/google/ghost-kernel.git && cd ghost_kernel`
3. Copy the config file to source code directory 
`$ cp /boot/cp /boot/config-5.10.103-meson64 .config `
4. Remove the signature checking certificates
`$ make menuconfig`
Remove 'debian/canonical-certs.pem' in Cryptographic API -> Certificates for signature checking
5. Start to compile  `make -j4`
6. Install the kernel module
`$ sudo make INSTALL_MOD_STRIP=1 modules_install # strip the modules to reduce the size of initrd`
Or
```
    $ sudo make install
    $ cd /lib/modules/<new_kernel> 
    $ find . -name *.ko -exec strip --strip-unneeded {} +
```
7.  After executing above command, proceed to create initramfs/initrd
```
    $ sudo make install
    $ sudo ln -s vmlinuz-5.11.0+ Image
```
8. Reboot and check the version of new kernel
```
    $ sudo reboot 
    $ uname -a to check the kernel
```
It should output the new kernel version which is `5.11.0+`: ` Linux ubuntu 5.11.0+ #2 SMP PREEMPT Mon Apr 18 00:50:21 UTC 2022 aarch64 aarch64 aarch64 GNU/Linux`
9. Finally install the headers
` sudo make headers_install INSTALL_HDR_PATH=/usr`
10. Have fun
