#!/usr/bin/env bash
set +H
export LC_ALL=C
umask 022
IFS=$' \t\n'
return 0 2>/dev/null || true
