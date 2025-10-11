#!/usr/bin/env sh
# Usage: ./lrc_denoms_union_kplus1.sh [denoms_by_k.txt] [lrc_structured.csv]
IN="${1:-denoms_by_k.txt}"
SRC="${2:-lrc_structured.csv}"

# collect the set of k from the structured CSV (col 2)
awk -F, 'NR>1{S[$2]=1} END{for(k in S) print k}' "$SRC" | sort -n > .kset

# normalize the learned denom map to "k: d1 d2 d3 ..."
awk -F, '{M[$1]=(M[$1]?M[$1]" "$2:$2)} END{for(k in M) print k":"M[k]}' "$IN" > .dmap

: > denoms_plus.txt
while read -r k; do
  have="$(awk -F: -v k="$k" '$1==k{print $2}' .dmap)"
  { echo "$have"; echo "$((k+1))"; } \
  | tr ' ' '\n' | awk 'NF' | sort -n | uniq \
  | while read -r d; do
      echo "$k,$d" >> denoms_plus.txt
    done
done < .kset

rm -f .kset .dmap
