#!/usr/bin/env bash
set +H; set -euo pipefail
DATA=${1:-"/c/Users/Cody/Downloads/LS3D-W/LS3D-W"}
OUT=${2:-"analysis/geom/ls3dw_mat_manifest.tsv"}
TMP="analysis/geom/.ls3dw_tmp.tsv"
mkdir -p "$(dirname "$OUT")"
rm -f "$OUT" "$TMP"
printf "path\tsize_bytes\tsha256\n" >> "$OUT"
find "$DATA" -type f -name "*.mat" -print0 | while IFS= read -r -d "" F; do
  [ -f "$F" ] || continue
  SZ=$(wc -c < "$F" | tr -d "\r\n[:space:]")
  H=$(sha256sum "$F" | awk "{print \$1}")
  printf "%s\t%s\t%s\n" "$F" "$SZ" "$H" >> "$TMP"
done
[ -s "$TMP" ] && sort "$TMP" | uniq >> "$OUT"
rm -f "$TMP"
