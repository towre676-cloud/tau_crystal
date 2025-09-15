#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
OUT="analysis/bash_theta_scan.tsv"
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"

readv(){ f="$1"; k="$2"; sed -n "s/^${k}=\\(.*\\)$/\\1/p" "$f" 2>/dev/null | head -n1; }
S1="$(readv "$best" BEST_S_MICRO)"; T1="$(readv "$best" BEST_T_MICRO)"
S2="$(readv "$sec"  BEST_S_MICRO)"; T2="$(readv "$sec"  BEST_T_MICRO)"
[ -n "$S1$T1" ] || { echo "[proxy2] missing best witness"; exit 0; }
: "${S2:=$S1}"; : "${T2:=$T1}"

padS=${S_PAD:-50000}; padT=${T_PAD:-50000}; stepS=${S_STEP:-2000}; stepT=${T_STEP:-2000}
min(){ a="$1"; b="$2"; [ "$a" -lt "$b" ] && echo "$a" || echo "$b"; }
max(){ a="$1"; b="$2"; [ "$a" -gt "$b" ] && echo "$a" || echo "$b"; }
S_MIN=$(( $(min "$S1" "$S2") - padS )); S_MAX=$(( $(max "$S1" "$S2") + padS ))
T_MIN=$(( $(min "$T1" "$T2") - padT )); T_MAX=$(( $(max "$T1" "$T2") + padT ))

: > "$OUT"; printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "S_micro" "T_micro" "diff" "mA" "mB" "nA" "nB" >> "$OUT"

for S in $(seq "$S_MIN" "$stepS" "$S_MAX"); do   # NOTE: START STEP END
  for T in $(seq "$T_MIN" "$stepT" "$T_MAX"); do # NOTE: START STEP END
    ds1=$(( S - S1 )); ds1=${ds1#-}; dt1=$(( T - T1 )); dt1=${dt1#-}
    d1=$(isqrt $(( ds1*ds1 + dt1*dt1 )))
    ds2=$(( S - S2 )); ds2=${ds2#-}; dt2=$(( T - T2 )); dt2=${dt2#-}
    d2=$(isqrt $(( ds2*ds2 + dt2*dt2 )))
    D=$(( d1<d2 ? d1 : d2 ))
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$S" "$T" "$D" "$S" "$T" 1 1 >> "$OUT"
  done
done
echo "[proxy2] wrote $OUT"
