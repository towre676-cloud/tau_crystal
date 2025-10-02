#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
ts="$(date -u +%Y%m%d_%H%M%SZ)"; M="docs/monographs/langlands_phase_next_${ts}.md"
: > "$M"
printf "%s\n" "# τ-Crystal Langlands Observatory — Phase-Next Report (${ts}Z)" >> "$M"
printf "%s\n\n" "This monograph records the reciprocity ecology, parameter terrain, spectral checks, and ledger anchors produced by the bash-native observatory." >> "$M"
if [ -s analysis/reciprocity_best.env ]; then printf "%s\n" "Primary witness: S=$(awk -F= '$1=="BEST_S_MICRO"{print $2}' analysis/reciprocity_best.env)  T=$(awk -F= '$1=="BEST_T_MICRO"{print $2}' analysis/reciprocity_best.env)" >> "$M"; fi
if [ -s analysis/reciprocity_second.env ]; then printf "%s\n" "Secondary: $(tr "\n" " " < analysis/reciprocity_second.env)" >> "$M"; fi
[ -s analysis/morse_crit.tsv ] && printf "%s\n" "Morse points: $(($(wc -l < analysis/morse_crit.tsv)-1))" >> "$M"
[ -s analysis/feq_report.txt ] && { printf "%s\n" "" >> "$M"; tail -n +1 analysis/feq_report.txt >> "$M"; }
[ -s analysis/ramanujan.tsv ] && { printf "%s\n\n" "" >> "$M"; printf "%s\n" "Ramanujan summary:" >> "$M"; tail -n +5 analysis/ramanujan.tsv | awk 'END{print "rows:",NR}' >> "$M"; }
[ -s analysis/trace_formula.tsv ] && { printf "%s\n\n" "" >> "$M"; cat analysis/trace_formula.tsv >> "$M"; }
printf "%s\n\n" "" >> "$M"; echo "[monograph] wrote $M"
