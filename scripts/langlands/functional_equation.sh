#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
rep="analysis/feq_report.txt"; : > "$rep"
ords="analysis/double_zero_ords.tsv"
[ -s "$ords" ] || ords=".tau_ledger/automorphic/new_zeros.json"
[ -s "$ords" ] || { echo "[skip] no zeros source found" | tee -a "$rep"; exit 0; }
tmp="$(mktemp)";
case "$ords" in *.tsv) awk 'NR>1{print $1}' "$ords" > "$tmp";; *.json) tr -d "\r\n\t " < "$ords" | sed "s/\[/\n/g;s/\]/\n/g;s/,/\n/g" | awk 'NF{print $1}' > "$tmp";; esac
N=$(wc -l < "$tmp" | tr -d "[:space:]"); [ "$N" -eq 0 ] && { echo "[skip] no ordinates parsed" | tee -a "$rep"; rm -f "$tmp"; exit 0; }
echo "functional-equation proxy: symmetry of zeros around t -> -t, center=0 (critical line proxy)" >> "$rep"
awk '{x=$1; gsub(/[^\-0-9.]/,"",x); if(x=="") next; pos[(x<0?-x:x)]++} END{m=0; im=0; for(k in pos){if(pos[k]==2) m++; else im++;} print "paired:",m,"unpaired:",im}' "$tmp" >> "$rep"
rm -f "$tmp"; echo "[ok] wrote $rep"
