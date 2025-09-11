#!/usr/bin/env bash
set -Eeuo pipefail; set +H
L="${1:-lakefile.lean}"
[ -s "$L" ] || { echo "[err] not found: $L" >&2; exit 2; }
B="$L.bak.dups.$(date -u +%Y%m%d-%H%M%S)"; cp -f -- "$L" "$B"
