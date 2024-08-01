#!/usr/bin/python3
# -*- coding: utf-8 -*-

# Copyright (C) 2018 SUSE LLC
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
# USA.

"""
Script to sort series.conf lines according to the upstream order of commits that
the patches backport.

The script can either read series.conf lines (or a subset thereof) from stdin or
from the file named in the first argument.

A convenient way to use series_sort.py to filter a subset of lines
within series.conf when using the vim text editor is to visually
select the lines and filter them through the script:
    shift-v
    j j j j [...] # or ctrl-d or /pattern<enter>
    :'<,'>! ~/<path>/series_sort.py
"""

import argparse
import os
import sys

import pygit2_wrapper as pygit2

sys.path.append(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../python"))
import suse_git.exc as exc
import git_sort
import lib
import series_conf


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Sort series.conf lines according to the upstream order of "
        "commits that the patches backport.")
    parser.add_argument("-p", "--prefix", metavar="DIR",
                        help="Search for patches in this directory. Default: "
                        "current directory.")
    parser.add_argument("-c", "--check", action="store_true",
                        help="Report via exit status 2 if the series is not "
                        "sorted. Default: false.")
    parser.add_argument("-u", "--upstream", action="store_true",
                        help="Move patches upstream between subsystem sections "
                        "as appropriate. Default: false.")
    parser.add_argument("series", nargs="?", metavar="series.conf",
                        help="series.conf file which will be modified in "
                        "place. Default: if stdin is a terminal, "
                        "\"series.conf\"; otherwise, read input from stdin.")
    args = parser.parse_args()

    repo_path = lib.repo_path()
    repo = pygit2.Repository(repo_path)
    index = git_sort.SortIndex(repo)
    if git_sort.remotes[0] not in index.repo_heads:
        print("WARNING: Did not find a remote fetching from \"%s\" in LINUX_GIT remotes." %
              (git_sort.remotes[0].repo_url.url,))

    filter_mode = False
    if args.series is None:
        if sys.stdin.isatty():
            path = "series.conf"
        else:
            filter_mode = True
    else:
        path = args.series
    if filter_mode:
        f = sys.stdin
    else:
        try:
            f = open(path)
        except FileNotFoundError as err:
            print("Error: %s" % (err,), file=sys.stderr)
            sys.exit(1)
        series_path = os.path.abspath(path)
    lines = f.readlines()

    if args.prefix is not None:
        os.chdir(args.prefix)

    try:
        before, inside, after = series_conf.split(lines)
    except exc.KSNotFound as err:
        if filter_mode:
            before = []
            inside = lines
            after = []
        elif args.check:
            # no sorted section
            sys.exit(0)
        else:
            print("Error: %s" % (err,), file=sys.stderr)
            sys.exit(1)

    try:
        input_entries = lib.parse_inside(index, inside, args.upstream)
    except exc.KSError as err:
        print("Error: %s" % (err,), file=sys.stderr)
        sys.exit(1)

    try:
        sorted_entries = lib.series_sort(index, input_entries)
    except exc.KSError as err:
        print("Error: %s" % (err,), file=sys.stderr)
        sys.exit(1)

    new_inside = lib.flatten([
        lib.series_header(inside),
        lib.series_format(sorted_entries),
        lib.series_footer(inside),
    ])

    to_update = list(filter(lib.tag_needs_update, input_entries))
    if args.check:
        result = 0
        if inside != new_inside:
            print("Input is not sorted.")
            result = 2
        if len(to_update):
            print("Git-repo tags are outdated.")
            result = 2
        sys.exit(result)
    else:
        output = lib.flatten([
            before,
            new_inside,
            after,
        ])

        if filter_mode:
            f = sys.stdout
        else:
            f = open(series_path, mode="w")
        f.writelines(output)
        try:
            lib.update_tags(index, to_update)
        except exc.KSError as err:
            print("Error: %s" % (err,), file=sys.stderr)
            sys.exit(1)
