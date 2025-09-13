#!/usr/bin/env bash
set -Eeuo pipefail; set +H
in="$1"; out="$2"
[ -n "$in" ] && [ -n "$out" ] || { echo "[err] usage: _normalize.sh <in> <out>" >&2; exit 2; }
tr -d "\r" < "$in" | sed -E "s/[[:space:]]+$//" > "$out".lf
mv "$out".lf "$out"
