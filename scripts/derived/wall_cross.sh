#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
FROM="${1:?from heart}"; TO="${2:?to heart}"; FUN="${3:-tilt-along-stable}"
DST="analysis/derived/equivalences"; mkdir -p "$DST"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"; OUT="$DST/${FROM}_to_${TO}.$STAMP.json"; : > "$OUT"
TMP="$(mktemp -u).json"; : > "$TMP"
scripts/derived/_json.sh "$TMP" functor "$FUN" B5_equivariance "yes" note "derived equivalence (wall-crossing)" >/dev/null
W="__RAW__$(cat "$TMP")"
scripts/derived/_json.sh "$OUT" from "$FROM" to "$TO" witness "$W" >/dev/null
rm -f "$TMP"; echo "$OUT"
