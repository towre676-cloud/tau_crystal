#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_perturb.sh <in.tsv> <colname> <eps_rel> <out.tsv> }"
COL="${2:?}"; EPS="${3:?}"; OUT="${4:?}"
awk -v COL="$COL" -v EPS="$EPS" 'BEGIN{FS=OFS="\t"}
NR==1{
  for(i=1;i<=NF;i++){ name[$i]=i }
  if(!(COL in name)){ print "ERROR: no such column: " COL > "/dev/stderr"; exit 2 }
  idx=name[COL]; print $0; next
}
{
  $idx = sprintf("%.9f", ($idx+0.0)*(1.0+EPS));
  print $0
}' "$IN" > "$OUT"
