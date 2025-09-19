#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
echo "[morpho-ci] start"
IN="analysis/morpho/input"; OUT="analysis/morpho/output"; LED="analysis/morpho/ledger"; mkdir -p "$OUT" "$LED"
if [ ! -d "$IN" ] || [ -z "$(ls -A "$IN" 2>/dev/null)" ]; then echo "[morpho-ci] no inputs; skipping analysis"; echo "{}" > "$OUT/morpho_report.json"; printf "%s\n" "# Morphometric Receipt (empty run)" > "$OUT/morpho_report.md"; exit 0; fi
if [ ! -x "scripts/morpho/analyze_basic.sh" ]; then echo "[morpho-ci] analyzer missing; skipping"; echo "{}" > "$OUT/morpho_report.json"; printf "%s\n" "# Morphometric Receipt (no analyzer)" > "$OUT/morpho_report.md"; exit 0; fi
echo "[morpho-ci] running analyzer"
scripts/morpho/analyze_basic.sh "$IN/frontal.jpg" "$IN/left.jpg" "$IN/right.jpg" "$OUT" || { echo "[morpho-ci] analyzer failed"; exit 2; }
echo "[morpho-ci] post-check: refuse to upload raw images"
find "$OUT" -maxdepth 1 -type f \( -iname "*.jpg" -o -iname "*.jpeg" -o -iname "*.png" -o -iname "*.heic" \) -print -quit | grep -q . && { echo "[morpho-ci] found image in OUT; refusing"; exit 3; }
echo "[morpho-ci] ok"; ls -l "$OUT" || true; ls -l "$LED" || true
