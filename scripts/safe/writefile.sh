#!/usr/bin/env bash
. "$(dirname "$0")/_env.sh"
set -e
p="$1"; shift || true
[ -n "$p" ] || { echo "usage: writefile.sh <path> [line ...]" >&2; exit 2; }
d=$(dirname "$p"); [ -d "$d" ] || mkdir -p "$d"
tmp="$p.tmp.$$"
> "$tmp"
for L in "$@"; do printf "%s\n" "$L" >> "$tmp"; done
mv -f "$tmp" "$p"
