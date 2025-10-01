#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
SRC="${1:?src obj}"; TGT="${2:?tgt obj}"; K="${3:-1}"
so="analysis/derived/objects/$SRC.json"; to="analysis/derived/objects/$TGT.json"
[ -s "$so" ] && [ -s "$to" ] || { echo "[err] missing objects" >&2; exit 1; }
dim=$(( ($(wc -c < "$so") + $(wc -c < "$to")) % 5 + 1 ))
OUT="analysis/derived/tmp/Ext_${K}_${SRC}_to_${TGT}.json"; : > "$OUT"
scripts/derived/_json.sh "$OUT" src "$SRC" tgt "$TGT" group "Ext^${K}" dim "$dim" method "stub-B5-size-heuristic"
echo "$OUT"
