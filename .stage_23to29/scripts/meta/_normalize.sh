#!/usr/bin/env bash
set -Eeuo pipefail; set +H
in="$1"; out="$2"
[ -n "$in" ] && [ -n "$out" ] || { echo "[err] $0: operation failed; check input and try again
tr -d "\r" < "$in" | sed -E "s/[ \t]+$//" > "$out".lf
mv "$out".lf "$out"
