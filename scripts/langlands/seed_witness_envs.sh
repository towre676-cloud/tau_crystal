#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
scan="analysis/bash_theta_scan.tsv"; morse="analysis/morse_crit.tsv"
# best: from Morse minima → else from scan minima → else leave as-is
if [ ! -s "$best" ]; then
  if [ -s "$morse" ]; then awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' "$morse" | sort -k3,3n | awk 'NR==1{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$best";
  elif [ -s "$scan" ]; then awk -F"\t" 'NR>1{print $1"\t"$2"\t"$3}' "$scan" | sort -k3,3n | awk 'NR==1{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$best"; fi
fi
# second: from 2nd Morse min → else 2nd scan min → else synthesize offset from best
if [ ! -s "$sec" ]; then
  if [ -s "$morse" ] && awk -F"\t" '$4=="min"{c++} END{exit(c<2)}' "$morse"; then
    awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' "$morse" | sort -k3,3n | awk 'NR==2{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$sec";
  elif [ -s "$scan" ] && [ "$(awk 'END{print NR}' "$scan")" -gt 2 ]; then
    awk -F"\t" 'NR>1{print $1"\t"$2"\t"$3}' "$scan" | sort -k3,3n | awk 'NR==2{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$sec";
  elif [ -s "$best" ]; then
    bS=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' "$best"); bT=$(awk -F= '$1=="BEST_T_MICRO"{print $2}' "$best");
    dS=${S_STEP:-20000}; dT=${T_STEP:--12000}; printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n" "$((bS+dS))" "$((bT+dT))" > "$sec";
  fi
fi
bS=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' "$best" 2>/dev/null | head -n1)
sS=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' "$sec"  2>/dev/null | head -n1)
echo "[seed] best=${bS:-} second=${sS:-}"
