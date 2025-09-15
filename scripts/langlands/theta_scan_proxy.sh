#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
OUT="analysis/bash_theta_scan.tsv"
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
readv(){ f="$1"; k="$2"; awk -F= -v k="$k" '$1==k{gsub(/\r/,"",$2);print $2}' "$f" 2>/dev/null | head -n1; }
: > "$OUT"; printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "S_micro" "T_micro" "diff" "mA" "mB" "nA" "nB" >> "$OUT"
S_MIN=${S_MIN:-} S_MAX=${S_MAX:-} S_STEP=${S_STEP:-} T_MIN=${T_MIN:-} T_MAX=${T_MAX:-} T_STEP=${T_STEP:-}
if [ -z "$S_MIN" ] || [ -z "$S_MAX" ] || [ -z "$S_STEP" ] || [ -z "$T_MIN" ] || [ -z "$T_MAX" ] || [ -z "$T_STEP" ]; then
  S1=$(readv "$best" BEST_S_MICRO); T1=$(readv "$best" BEST_T_MICRO); S2=$(readv "$sec" BEST_S_MICRO); T2=$(readv "$sec" BEST_T_MICRO)
  : "${S2:=$S1}"; : "${T2:=$T1}"
  padS=${S_PAD:-50000}; padT=${T_PAD:-50000}; stepS=${S_STEP:-2000}; stepT=${T_STEP:-2000}
  min(){ a="$1"; b="$2"; [ "$a" -lt "$b" ] && echo "$a" || echo "$b"; }
  max(){ a="$1"; b="$2"; [ "$a" -gt "$b" ] && echo "$a" || echo "$b"; }
  S_MIN=$(( $(min "$S1" "$S2") - padS )); S_MAX=$(( $(max "$S1" "$S2") + padS ))
  T_MIN=$(( $(min "$T1" "$T2") - padT )); T_MAX=$(( $(max "$T1" "$T2") + padT ))
  S_STEP=$stepS; T_STEP=$stepT
fi
tmp="$(mktemp)"; printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "S_micro" "T_micro" "diff" "mA" "mB" "nA" "nB" > "$tmp"
for S in $(seq "$S_MIN" "$S_STEP" "$S_MAX"); do
  for T in $(seq "$T_MIN" "$T_STEP" "$T_MAX"); do
    ds=$(( S - S1 )); ds=${ds#-}; dt=$(( T - T1 )); dt=${dt#-}
    d2=$(( ds*ds + dt*dt )); D=$(isqrt "$d2")
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$S" "$T" "$D" "$S" "$T" 1 1 >> "$tmp"
  done
done
mv -f "$tmp" "$OUT"; echo "[proxy] wrote $OUT"
