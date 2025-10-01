#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
NAME="${1:?heart name}"; PHI="${2:-0.5}"; ZR="${3:-1.0}"
DST="analysis/derived/hearts"; mkdir -p "$DST"; OUT="$DST/$NAME.json"; : > "$OUT"
TMP="$(mktemp -u).json"; : > "$TMP"
scripts/derived/_json.sh "$TMP" phase "$PHI" central_charge "$ZR" note "seed stability" >/dev/null
STAB="__RAW__$(cat "$TMP")"
scripts/derived/_json.sh "$OUT" heart "$NAME" chamber "$NAME" stability "$STAB" >/dev/null
rm -f "$TMP"; echo "$OUT"
