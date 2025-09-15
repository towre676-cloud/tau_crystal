#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
[ -s "$best" ] || {
  awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' analysis/morse_crit.tsv 2>/dev/null | sort -k3,3n |
  awk 'NR==1{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$best" || true
}
[ -s "$sec" ] || {
  awk -F"\t" '$4=="min"{print $1"\t"$2"\t"$3}' analysis/morse_crit.tsv 2>/dev/null | sort -k3,3n |
  awk 'NR==2{printf "BEST_S_MICRO=%s\nBEST_T_MICRO=%s\n",$1,$2}' > "$sec" || true
}
echo "[seed] best=$(sed -n "\"s/^BEST_S_MICRO=//p\"" "$best" | head -n1), second=$(sed -n "\"s/^BEST_S_MICRO=//p\"" "$sec" | head -n1)"
