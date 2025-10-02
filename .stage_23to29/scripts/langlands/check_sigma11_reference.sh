#!/usr/bin/env bash
set +H
umask 022
REF="analysis/validation/tau_reference.tsv"
OUT="analysis/validation/sigma11_congruence.tsv"
[ ! -f "$REF" ] && { echo "missing: $REF" >&2; exit 2; }
: > "$OUT"
printf "n\ttau(n)\tsigma11(n)\t(τ-σ11)%%691\tok_mod_691\n" >> "$OUT"
awk -F"\t" 'function sigma11(n,  d,t,s){ s=0; for(d=1; d*d<=n; d++){ if(n%d==0){ s+=d^11; if(d*d!=n){ t=int(n/d); s+=t^11 } } } return s } BEGIN{M=691} NR==1{next} { n=$1+0; tv=($3!=""?$2+0:$2+0); s=sigma11(n); diff=(($2+0)-s)%M; if(diff<0) diff+=M; ok=(diff==0?"yes":"no"); printf "%d\t%d\t%d\t%d\t%s\n", n,($2=="NA"?0:$2+0),s,diff,ok }' "$REF" >> "$OUT"
awk '{sub(/\r$/,""); print }' "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
echo "wrote $OUT"
