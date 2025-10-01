#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?morphism id}"; SRC="${2:?src}"; TGT="${3:?tgt}"; DEG="${4:-0}"; EQ="${5:-B5-equivariant}"
DST="analysis/derived/morphisms"; mkdir -p "$DST"; OUT="$DST/$ID.json"; : > "$OUT"
scripts/derived/_json.sh "$OUT" id "$ID" src "$SRC" tgt "$TGT" degree "$DEG" equivariance "$EQ"
echo "$OUT"
