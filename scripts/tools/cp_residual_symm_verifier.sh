#!/usr/bin/env bash
set -Eeuo pipefail; set +H
IN="${1:-analysis/morse_crit.tsv}"
TH_COL="${2:-1}"
VAL_COL="${3:-3}"
EPS="${EPS:-1e-9}"
OUT="${OUT:-analysis/cp_residual.tsv}"
STRICT="${STRICT:-1}"
mkdir -p "$(dirname "$OUT")"
if [ ! -s "$IN" ]; then
  echo "[cp] no data: $IN"
  printf "residual\tNaN\nepsilon\t%s\npairs\t0\npass\t0\n" "$EPS" > "$OUT"
  exit 4
fi
LC_ALL=C awk -F"\t" -v t="$TH_COL" -v v="$VAL_COL" -v eps="$EPS" -v strict="$STRICT" \
  -f scripts/tools/_cp_resid.awk "$IN" > "$OUT"
rc=$?
echo "[cp] resid=$(awk -F"\t" '$1=="residual"{print $2}' "$OUT") eps=$EPS pairs=$(awk -F"\t" '$1=="pairs"{print $2}' "$OUT")"
exit "$rc"
