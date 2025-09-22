#!/usr/bin/env bash
set +e; set +H; umask 022
# Usage: delta_from_mapping.sh src_leaf_tsv dst_leaf_tsv map.tsv > delta.tsv
SRC="$1"; DST="$2"; MAP="$3"
# Build count maps
awk '{c[$2]+=$3} END{for(k in c) print k"\t"c[k]}' "$SRC" | sort > "$MAP.src.counts"
awk '{c[$2]+=$3} END{for(k in c) print k"\t"c[k]}' "$DST" | sort > "$MAP.dst.counts"
# Push forward src counts along MAP
awk 'NR==FNR{m[$1]=$2; next} {d[$2]+=$2 in m?0:0} END{for(k in m) print k"\t"m[k]}' "$MAP" "$MAP" >/dev/null
awk 'NR==FNR{m[$1]=$2; next} {n=($1 in m)?m[$1]: ""; if(n!=""){pf[n]+= $2} } END{for(k in pf) print k"\t"pf[k]}' "$MAP" "$MAP.src.counts" | sort > "$MAP.push"
# Align and subtract: Δ_f = pushforward(src) - dst
join -a1 -a2 -e 0 -o 0,1.2,2.2 -t $'\t' "$MAP.push" "$MAP.dst.counts" | awk '{print $1"\t"($2-$3)}'
