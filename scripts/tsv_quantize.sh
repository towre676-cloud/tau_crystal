#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_quantize.sh <in.tsv> <decimals> <out.tsv> }"
DEC="${2:?}"; OUT="${3:?}"
awk -v DEC="$DEC" 'BEGIN{FS=OFS="\t"; fmt=sprintf("%%.%df", DEC)}
NR==1{ print $0; next }
{
  for(i=1;i<=NF;i++){
    if($i ~ /^-?[0-9]+(\.[0-9]*)?([eE][+-]?[0-9]+)?$/){ $i=sprintf(fmt, $i+0.0) }
  }
  print $0
}' "$IN" > "$OUT"
