#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?motive id}"; DEST="analysis/motive/objects/$ID/comparisons"; mkdir -p "$DEST"
OUT="$DEST/betti_derham.json"; : > "$OUT"
printf "{\n  \"motive\":\"%s\",\n  \"map\":\"comparison_isomorphism\",\n  \"matrix\":\"[[1,0],[0,1]]\",\n  \"note\":\"placeholder identity\"\n}\n" "$ID" >> "$OUT"
echo "[ok] comparison → $OUT"
