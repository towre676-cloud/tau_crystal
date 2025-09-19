#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
OUT="analysis/morpho/output"; PUB="analysis/morpho/public"; LED="analysis/morpho/ledger/morpho_receipts.jsonl"
mkdir -p "$PUB"
[ -s "$OUT/FACE.txt" ]  || { echo "[publish] missing $OUT/FACE.txt"; exit 3; }
[ -s "$OUT/face2.txt" ] || { echo "[publish] missing $OUT/face2.txt"; exit 4; }
cp -f "$OUT/FACE.txt"  "$PUB/FACE.txt"
cp -f "$OUT/face2.txt" "$PUB/face2.txt"
coin="$(awk -F: '/^coin/{gsub(/^[ \t]+/,"",$2); print $2}' "$OUT/FACE.txt" 2>/dev/null | tr -d "[:space:]")"
[ -n "$coin" ] && printf "%s\n" "$coin" > "$PUB/coin_id.txt" || true
git add "$PUB/FACE.txt" "$PUB/face2.txt" "$PUB/coin_id.txt" 2>/dev/null || true
git commit -m "morpho(public): publish FACE.txt + face2.txt for public crawl" 2>/dev/null || true
echo "[publish] public copies at analysis/morpho/public/{FACE.txt,face2.txt,coin_id.txt}"
