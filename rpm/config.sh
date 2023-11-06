# The version of the main tarball to use
SRCVERSION=6.6-next-20231106
# variant of the kernel-source package, either empty or "-rt"
VARIANT=-vanilla
# Set to 1 to use the variant kernel for kernel-obs-build
OBS_BUILD_VARIANT=1
# enable kernel module compression
COMPRESS_MODULES="xz"
# Compile binary devicetrees on master and stable branches.
BUILD_DTBS="Yes"
BUILD_HTML=Yes
BUILD_PDF=Yes
# buildservice projects to build the kernel against
OBS_PROJECT=openSUSE:Factory
OBS_PROJECT_ARM=openSUSE:Factory:ARM
OBS_PROJECT_PPC=openSUSE:Factory:PowerPC
IBS_PROJECT=SUSE:Factory:Head
IBS_PROJECT_ARM=Devel:ARM:Factory
