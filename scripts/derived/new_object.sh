#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?id}"; REP="${2:-triv}"; DEG="${3:-0}"; CH="${4:-leaf_A}"
DST="analysis/derived/objects"; mkdir -p "$DST"; OUT="$DST/$ID.json"; : > "$OUT"
INV="__RAW__{\"rank\":1,\"chern\":\"0\",\"note\":\"seed\"}"
scripts/derived/_json.sh "$OUT" id "$ID" rep "$REP" degree "$DEG" chamber "$CH" invariants "$INV"
echo "$OUT"
