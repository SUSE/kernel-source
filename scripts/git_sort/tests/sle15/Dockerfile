# http://registry.suse.de/
FROM registry.suse.de/suse/containers/sle-server/15/containers/bci/python:3.9 AS base

RUN rpm -e container-suseconnect
RUN zypper -n ar -G http://download.suse.de/ibs/SUSE:/SLE-15:/GA/standard/SUSE:SLE-15:GA.repo
RUN zypper -n ar -G http://download.suse.de/ibs/SUSE:/SLE-15:/Update/standard/SUSE:SLE-15:Update.repo
RUN zypper -n ref

FROM base AS packages

RUN zypper -n in git-core python3 python3-dbm rcs awk

RUN git config --global user.email "you@example.com"
RUN git config --global user.name "Your Name"

RUN zypper -n ar -G https://download.opensuse.org/repositories/Kernel:/tools/SLE_15/Kernel:tools.repo
RUN zypper -n in python3-pygit2 quilt

FROM packages

VOLUME /scripts

WORKDIR /scripts/git_sort

CMD python3 -m unittest discover -v
