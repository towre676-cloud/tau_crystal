#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
out="analysis/deformation_ring.tsv"; dot="analysis/deformation_ring.dot"
: > "$out"; printf "%s\n" "name\tS_micro\tT_micro" >> "$out"
for f in analysis/reciprocity_best.env analysis/reciprocity_second.env; do [ -s "$f" ] || continue; S=$(read_kv "$f" BEST_S_MICRO); T=$(read_kv "$f" BEST_T_MICRO); n=$(basename "$f" .env); printf "%s\n" "$n	$S	$T" >> "$out"; done
: > "$dot"; printf "%s\n" "graph G {" >> "$dot"
awk 'NR==1{next} {print "  \"" $1 "\" [label=\"" $1 "\\nS=" $2 "\\nT=" $3 "\"];"}' "$out" >> "$dot"
if [ -s "analysis/morse_crit.tsv" ]; then awk 'NR==1{next} $4=="saddle"{print; ss[$1 FS $2]=1}' analysis/morse_crit.tsv >/dev/null 2>&1; fi
awk 'NR==1{next} {K[NR]=$0; n=NR} END{for(i=2;i<=n;i++) for(j=i+1;j<=n;j++){split(K[i],a,"\t"); split(K[j],b,"\t"); ds=a[2]-b[2]; dt=a[3]-b[3]; if(ds<0) ds=-ds; if(dt<0) dt=-dt; if(ds+dt<=20000) print "  \"" a[1] "\" -- \"" b[1] "\";"; }}' "$out" >> "$dot"
printf "%s\n" "}" >> "$dot"
