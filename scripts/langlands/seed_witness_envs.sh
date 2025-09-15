#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
scan="analysis/bash_theta_scan.tsv"; morse="analysis/morse_crit.tsv"
# if best missing, try Morse minima; else try scan minima; else do nothing
if [ ! -s "$best" ]; then
  if [ -s "$morse" ]; then
    awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' "$morse" | sort -k3,3n | awk 'NR==1{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$best" 2>/dev/null
  elif [ -s "$scan" ]; then
    awk -F"\t" 'NR>1{print $1"\t"$2"\t"$3}' "$scan" | sort -k3,3n | awk 'NR==1{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$best" 2>/dev/null
  fi
fi
if [ ! -s "$sec" ]; then
  if [ -s "$morse" ]; then
    awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' "$morse" | sort -k3,3n | awk 'NR==2{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$sec" 2>/dev/null
  elif [ -s "$scan" ]; then
    awk -F"\t" 'NR>1{print $1"\t"$2"\t"$3}' "$scan" | sort -k3,3n | awk 'NR==2{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$sec" 2>/dev/null
  fi
fi
bS=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' "$best" 2>/dev/null | head -n1)
sS=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' "$sec"  2>/dev/null | head -n1)
echo "[seed] best=${bS:-} second=${sS:-}"
