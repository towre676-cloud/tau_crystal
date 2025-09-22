#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seqfile="${1:-.tau_ledger/seq/tau.csv}"
out=".tau_ledger/metrics/dim_tau.json"
[ -s "$seqfile" ] || { echo "{\"dim_tau\":null,\"error\":\"missing tau.csv\"}" > "$out"; exit 0; }
tmp="$(mktemp)"; awk -F, "NR>1{print \$2}" "$seqfile" > "$tmp" || true
[ -s "$tmp" ] || { echo "{\"dim_tau\":null,\"error\":\"no tau values\"}" > "$out"; rm -f "$tmp"; exit 0; }
awk 'BEGIN{eps=1e-12}{x[NR]=$1}END{n=NR-0; if(n<8){print "{\"dim_tau\":null,\"warn\":\"short series\"}"; exit} for(i=2;i<=n;i++){d[i-1]=x[i]-x[i-1]; a[i-1]= (d[i-1]<0?-d[i-1]:d[i-1]) } m=0; for(i=1;i<=n-1;i++){if(a[i]>0) m+=log(a[i]+eps)} m/= (n-1); # coarse slope proxy
  # windowed second‑scale
  w=int(n/4); if(w<3) w=3; s1=0; c=0; for(i=1;i<=n-1-w;i++){acc=0; for(j=0;j<w;j++){ad=a[i+j]; if(ad<=0) ad=eps; acc+=log(ad)} s1+=acc/w; c++ } if(c==0){print "{\"dim_tau\":null,\"warn\":\"window fail\"}"; exit}
  slope=(s1/c - m); dim= (slope<0?-slope:slope); if(dim>8) dim=8; if(dim<0) dim=0; printf("{\"dim_tau\":%.6f}\n", dim) }' "$tmp" > "$out"
rm -f "$tmp"; echo "$out"
