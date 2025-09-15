#!/usr/bin/env bash
set -Ee -o pipefail; set +H

SRC="${1:-analysis/bash_theta_scan.tsv}"
[ -s "$SRC" ] || { echo "[err] missing or empty TSV: $SRC" >&2; exit 2; }

bestd=999999999
best=""
# read TSV safely (skip header)
exec 9<"$SRC"
IFS= read -r _hdr <&9 || true
while IFS= read -r line <&9; do
  [ -z "${line:-}" ] && continue
  first="${line%%[ 	]*}"; case "$first" in S_micro*|"#"*) continue;; esac
  # parse columns
  set -- $line
  S="${1:-}"; T="${2:-}"; D="${3:-}"; mA="${4:-}"; mB="${5:-}"; nA="${6:-}"; nB="${7:-}"
  [ -z "$S" ] || [ -z "$D" ] && continue
  # sign-safe ints
  D=$(( D + 0 ))
  if [ "$D" -lt "$bestd" ]; then
    bestd="$D"; best="$line"
  fi
done
exec 9<&-

[ -n "$best" ] || { echo "[err] no data rows in TSV (only header?)" >&2; exit 3; }

mkdir -p analysis
: > analysis/reciprocity_best.tsv
printf '%s\n' "S_micro	T_micro	diff	mA	mB	nA	nB" >> analysis/reciprocity_best.tsv
printf '%s\n' "$best" >> analysis/reciprocity_best.tsv

# extract fields
set -- $best
S="$1"; T="$2"; D="$3"; mA="$4"; mB="$5"; nA="$6"; nB="$7"

# micro→decimal (sign-safe) helper
micro_to_dec() {
  local x="$1" s=""
  [ "$x" -lt 0 ] && s="-" && x=$(( -x ))
  local i=$(( x/1000000 ))
  local f=$(( x%1000000 ))
  printf "%s%d.%06d" "$s" "$i" "$f"
}

: > analysis/reciprocity_best.env
printf 'BEST_S_MICRO=%s\nBEST_T_MICRO=%s\nBEST_D_MICRO=%s\n' "$S" "$T" "$D" >> analysis/reciprocity_best.env
printf 'BEST_S_DEC=%s\n' "$(micro_to_dec "$S")" >> analysis/reciprocity_best.env
printf 'BEST_T_DEC=%s\n' "$(micro_to_dec "$T")" >> analysis/reciprocity_best.env
printf 'BEST_mA=%s\nBEST_mB=%s\nBEST_nA=%s\nBEST_nB=%s\n' "$mA" "$mB" "$nA" "$nB" >> analysis/reciprocity_best.env

: > analysis/reciprocity_best.txt
{
  echo "tau-crystal reciprocity best (bash)"
  echo "-----------------------------------"
  echo "Δ(µ):   $D"
  echo "S:      $S  (dec: $(micro_to_dec "$S"))"
  echo "T:      $T  (dec: $(micro_to_dec "$T"))"
  echo "mA/mB:  $mA / $mB"
  echo "nA/nB:  $nA / $nB"
} >> analysis/reciprocity_best.txt

echo "[best] Dµ=$D  Sµ=$S  Tµ=$T  (S=$(micro_to_dec "$S"), T=$(micro_to_dec "$T"))"
