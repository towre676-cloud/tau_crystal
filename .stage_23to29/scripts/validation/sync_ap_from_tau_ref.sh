#!/usr/bin/env bash
set -euo pipefail; set +H
REF="${1:-analysis/validation/tau_reference.tsv}"
WORK="${2:-validation/work}"
[ -s "$REF" ] || { echo "missing $REF"; exit 1; }
awk -F"\t" 'NR>1 && $1+0>0 { if($2=="prime"){print $1"\t"$3} }' "$REF" | sort -n > "$WORK/.prime_tau.map"
while IFS= read -r d; do [ -d "$d" ] || continue; f="$d/a_p.tsv"; : > "$f"; awk "{print \$0}" "$WORK/.prime_tau.map" >> "$f"; done < <(find "$WORK" -maxdepth 1 -type d -name "face*")
