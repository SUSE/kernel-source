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
When we want to backport a specific commit at its right position in the sorted
sub-series, it is most efficient to use sequence_patch.sh to expand the tree up
to the patch just before where the new commit will be added. The current script
prints out which patch that is. Use in conjunction with sequence-patch.sh:
    kernel-source$ ./scripts/sequence-patch.sh $(./scripts/git_sort/sequence-insert.py 5c8227d0d3b1)
"""

import argparse
import os
import os.path
import sys

sys.path.append(os.path.join(os.path.dirname(__file__), "../python"))
import suse_git.exc as exc
import lib


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Print the name of the patch over which the specified "
        "commit should be imported.")
    parser.add_argument("rev", help="Upstream commit id.")
    args = parser.parse_args()

    try:
        (name, delta,) = lib.sequence_insert(open("series.conf"), args.rev,
                                             None)
    except exc.KSException as err:
        print("Error: %s" % (err,), file=sys.stderr)
        sys.exit(1)

    print(name)
