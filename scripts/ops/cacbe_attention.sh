#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ATT=.cacbe/attention.tsv; LOG=${1:-.tau_ledger/cacbe/latest.tsv}
[ -f "$ATT" ] || exit 0
if [ -f .tau_ledger/cacbe/latest.tsv ]; then LOG=.tau_ledger/cacbe/latest.tsv; fi
TMP=.cacbe/.att.$$; : > "$TMP"; printf "%s\n" "code\tseverity\tcount\tattention" >> "$TMP"
while IFS=$'\t' read -r code sev cnt att; do
  [ "$code" = "code" ] && continue
  c=$cnt
  if [ -f "$LOG" ]; then c=$(awk -F'\t' -v k="$code" 'NR>1 && $1==k{n++} END{print n+0}' "$LOG") ; fi
  s=$sev; a=$(( s * c ))
  printf "%s\n" "${code}\t${s}\t${c}\t${a}" >> "$TMP"
done < "$ATT"
mv "$TMP" "$ATT"
sort -t$'\t' -k4,4nr -k2,2nr "$ATT" | awk 'BEGIN{OFS="\t"} NR==1{print; next} {print}' > .cacbe/attention_ranked.tsv
