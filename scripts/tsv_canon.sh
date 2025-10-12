
#!/usr/bin/env bash
# tsv_canon.sh <in.tsv> <out.tsv> — tab, stable header, numeric columns to %.15g, preserve 'seed'
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_canon.sh <in.tsv> <out.tsv>}"; OUT="${2:?}"
sed -i 's/\r$//' "$IN" 2>/dev/null || true
awk -v OFS="\t" '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
function idx(name,i){name=canon(name); for(i=1;i<=NF;i++) if(canon($i)==name) return i; return -1}
NR==1{
  hline=$0; split("",H); for(i=1;i<=NF;i++) H[i]=$i;
  i_seed=idx("seed");
  print hline; next
}
{
  # print fields 1..NF; for numeric fields use %.15g except the seed column
  for(i=1;i<=NF;i++){
    if(i==i_seed){ fmt=$i; }
    else{
      # treat everything except seed as numeric; format via %.15g
      # adding 0 forces numeric, preserving signs and exp notation on output
      fmt=sprintf("%.15g", $i+0);
    }
    printf("%s%s", fmt, (i<NF?OFS:ORS));
  }
}
' "$IN" > "$OUT"

