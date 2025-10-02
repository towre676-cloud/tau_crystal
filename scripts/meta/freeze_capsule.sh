#!/usr/bin/env bash
set -eu; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)" || exit 1
cap="${1:-}"; [ -n "$cap" ] || { echo "[err] usage: freeze_capsule.sh <capsule_name>"; exit 2; }
dst="capsules/.freeze/${cap}_$(date -u +%Y%m%dT%H%M%SZ)_canon.json"; mkdir -p "$(dirname "$dst")"
[ -f canon.json ] && cp -f canon.json "$dst" || { echo "[err] canon.json missing"; exit 3; }
echo "[ok] froze $cap -> $dst"
