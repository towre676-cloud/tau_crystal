#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:-analysis/validation/SIGNED_DATASET.receipt.tsv}"
[ -s "$REC" ] || { echo "missing $REC"; exit 1; }
awk -F"\t" '{face=$1; line=$0; n=split(line,a,"ap_tau_p"); if(n>1){split("",P); for(i=2;i<=n;i++){split(a[i],b,":"); split(b[1],c,"[^0-9]"); p=c[1]; split(b[0],d,":"); val=b[2]; gsub(/[^-0-9]/,"",val); if(p!=""&&val!="") P[p]=val;} if(length(P)>0){dir="validation/work/"face; system("mkdir -p "dir); out=dir"/a_p.tsv"; cmd=": > "out; system(cmd); for (pp in P){print pp "\t" P[pp] >> out} close(out)}} }' "$REC"
