#############################################################################
# Copyright (c) 2008,2009 Novell, Inc.
# All Rights Reserved.
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of version 2 of the GNU General Public License as
# published by the Free Software Foundation.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.   See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, contact Novell, Inc.
#
# To contact Novell about this file by physical or electronic mail,
# you may find current contact information at www.novell.com
#############################################################################

# to be sourced by scripts that need a GIT working directory

if git rev-parse HEAD >/dev/null 2>&1; then
    using_git=true
else
    using_git=false
    echo "WARNING: not in a GIT working directory, things might break." >&2
    echo >&2
fi
scripts_dir="$(dirname "$0")"

get_branch_name()
{
    if $using_git; then
        # FIXME: guess a branch name when a non-branch revision is checked
        # out
        local res=$(sed -ne 's|^ref: refs/heads/||p' "$(git rev-parse --git-dir)"/HEAD 2>/dev/null)
        echo "$res"
    fi
}

get_kernel_sig(){
    echo "${1%.*}.sign"
}

_find_tarball()
{
    local version=$1 suffixes=$2 dir subdir major suffix tarball sig dc

    set -- ${version//[.-]/ }
    if test $1 -le 2; then
        major=$1.$2
    else
        major=$1.x
    fi
    if test -z "$suffixes"; then
        if test -n "$(type -p xz)"; then
            suffixes="tar.xz tar.bz2 tar.gz"
        else
            suffixes="tar.bz2"
        fi
    fi
    for dir in . $LINUX_TAR_DIR {/mounts,/labs,}/mirror/kernel; do
        for subdir in "" "/v$major" "/testing" "/v$major/testing"; do
            for suffix in $suffixes; do
                tarball="$dir$subdir/linux-$version.$suffix"
                if test -r "$tarball"; then
                    sig="$(get_kernel_sig "$tarball")"
                    if ! [ -r "$sig" ] ; then
                        echo "Missing signature $sig for tarball $tarball" >&2
                        continue
                    fi
                    echo "Verifying $tarball" >&2
                    case $suffix in
                        *.gz) dc="gzip -dc";;
                        *.xz) dc="xzcat";;
                        *.bz2) dc="bzip2 -dc";;
                        *) echo "Unknown archive format $suffix" >&2
                            continue;;
                    esac
                    if ! $dc < "$tarball" | gpgv --keyring "$scripts_dir/linux.keyring" "$sig" - ; then
                        echo "$tarball signature $sig verification failed" >&2
                        continue
                    fi
                    echo "$tarball"
                    return
                fi
            done
        done
    done
}

_get_tarball_from_git()
{
    local version=$1 tag url=$2 default_url
    local libdir=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")
    local git

    git=$("$libdir"/linux_git.sh) || exit 1
    case "$version" in
    *next-*)
        tag=refs/tags/next-${version##*next-}
        default_url=git://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git
        ;;
    [0-9]*-g???????)
        tag="v$version"
        default_url=git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux-2.6.git
        ;;
    *)
        tag=refs/tags/"v$version"
        default_url=git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux-2.6.git
    esac
    [ -z "$url" ] && url=$default_url
    if ! git --git-dir="$git" cat-file -e "$tag" 2>/dev/null; then
        case "$tag" in
        refs/tags/*)
            git --git-dir="$git" fetch "$url" "$tag:$tag"
            ;;
        *)
            # v2.6.X.Y-rcZ-gabcdef1, not a real tag
            git --git-dir="$git" fetch --tags "$url" \
                refs/heads/master:refs/tags/latest
        esac
    fi
    git --git-dir="$git" archive --prefix="linux-$version/" "$tag"
}

get_tarball()
{
    local version=$1 suffix=$2 dest=$3 url=$4 tarball compress sig

    tarball=$(_find_tarball "$version" "$suffix")
    if test -n "$tarball"; then
        sig="$(get_kernel_sig "$dest/linux-$version.$suffix")"
        cp -p "$tarball" "$dest/linux-$version.$suffix.part" || exit
        cp -p "$(get_kernel_sig "$tarball")" "$sig.part" || exit
        mv "$dest/linux-$version.$suffix.part" "$dest/linux-$version.$suffix"
        mv "$sig.part" "$sig"
        cp -p "$scripts_dir/linux.keyring" "$dest"
        return
    fi
    # Reuse the locally generated tarball if already there
    tarball="$dest/linux-$version.$suffix"
    if test -e "$tarball"; then
        echo "Reusing $tarball" >&2
        sig="$(get_kernel_sig "$tarball")"
        if [ -e $sig ] ; then
            echo "Reusing $sig" >&2
            cp -p "$scripts_dir/linux.keyring" "$dest"
        fi
        return
    fi
    echo "Warning: could not find linux-$version.$suffix, trying to create it from git" >&2
    case "$suffix" in
    tar.bz2)
        compress="bzip2 -9"
        ;;
    tar.xz)
        compress="xz"
        ;;
    *)
        echo "Unknown compression format: $suffix" >&2
        exit 1
    esac
    set -o pipefail
    _get_tarball_from_git "$version" "$url" | $compress \
        >"$dest/linux-$version.$suffix.part"
    if test $? -ne 0; then
        exit 1
    fi
    mv "$dest/linux-$version.$suffix.part" "$dest/linux-$version.$suffix"
    set +o pipefail
}

unpack_tarball()
{
    local version=$1 dest=$2 url=$3 tarball

    tarball=$(_find_tarball "$version")
    mkdir -p "$dest"
    if test -n "$tarball"; then
        echo "Extracting $tarball"
        case "$tarball" in
        *.bz2) tar -xjf "$tarball" -C "$dest" --strip-components=1 ;;
        *.gz) tar -xzf "$tarball" -C "$dest" --strip-components=1 ;;
        *.xz) xz -d <"$tarball" | tar -xf - -C "$dest" --strip-components=1 ;;
        *) tar -xf "$tarball" -C "$dest" --strip-components=1 ;;
        esac
        return
    fi
    echo "Warning: could not find linux-$version.tar.(bz2|xz), trying to create it from git" >&2
    echo "alternatively you can put an unpatched kernel tree to $dest" >&2
    set -o pipefail
    _get_tarball_from_git "$version" "$url" | tar -xf - -C "$dest" --strip-components=1
    if test $? -ne 0; then
        rm -rf "$dest"
        exit 1
    fi
    set +o pipefail
}

get_git_remote() {
    local branch=$1
    local remote

    remote=$(git config --get branch.${branch}.remote)
    remote=${remote:-"<repository>"}
    echo "$remote"
}

get_git_user() {
    local remote=$1
    local user

    if [ "$remote" ]; then
        user=$(git remote -v show -n | awk '
            /^'$remote'/ && /\(push\)$/ {
                match($2, "^(ssh://)?(([^@]+)@)?", a)
                print a[3]
            }')
    fi
    user=${user:-$LOGNAME}
    user=${user:-"<user>"}
    echo "$user"
}

if $using_git && test -z "$CHECKED_GIT_HOOKS"; then
    export CHECKED_GIT_HOOKS=1
    if ! "$scripts_dir"/install-git-hooks --check; then
        echo "WARNING: You should run $scripts_dir/install-git-hooks to enable pre-commit checks." >&2
    fi
fi

get_localversion() {
    local version=$1

    if [[ "$version" =~ .*-[1-9][0-9]*-g[a-f0-9]+$ ]] # 4.4-rc6-1310-gec0382c
    then
	echo "$version" | sed -e "s/.*\(-[1-9][0-9]*-g[a-f0-9]\+\)$/\1/";
    fi
}

# vim: sw=4:sts=4:et
