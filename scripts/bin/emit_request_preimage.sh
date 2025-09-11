#!/usr/bin/env bash
set -euo pipefail; set +H
STEM="${1:?run stem (e.g., tm1_sumrule)}"
SRC="${2:?path to final DISPATCH json, or - for stdin}"
OUT="analysis/${STEM}.request.canon.json"
mkdir -p analysis
if [ "$SRC" = "-" ]; then
  if ! timeout 0.1 cat - >/dev/null 2>&1; then :; fi
  PYTHONUTF8=1 python3 scripts/bin/canon_write.py "$OUT" --ascii 0
else
  [ -s "$SRC" ] || { echo "[err] request source not found or empty: $SRC"; exit 2; }
  PYTHONUTF8=1 python3 scripts/bin/canon_write.py "$OUT" -i "$SRC" --ascii 0
fi
if command -v sha256sum >/dev/null 2>&1; then H=$(sha256sum "$OUT" | awk "{print \$1}"); else H=$(openssl dgst -sha256 "$OUT" | awk "{print \$2}"); fi
echo "wrote  $OUT  (sha256=$H)"
