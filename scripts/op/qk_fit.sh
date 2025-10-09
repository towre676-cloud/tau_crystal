#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
IN="${1:-./tmp/qk_corr.norm.tsv}"; OUT_JSON="./tmp/qk_fit.json"; OUT_RES="./tmp/qk_residuals.tsv"
[ -f "$IN" ] || { echo "[err] missing: $IN" >&2; exit 2; }
awk -v OFS="\t" -v J="$OUT_JSON" -v R="$OUT_RES" '
BEGIN{n=0;Sx=Sy=Sxx=Sxy=0; nlog=0;Sxl=Syl=Sx2l=Sxyl=0}
{ if(NF<3) next; k[++n]=$1; q[n]=$2; c[n]=$3; Sx+=q[n]; Sy+=c[n]; Sxx+=q[n]*q[n]; Sxy+=q[n]*c[n]; if(q[n]>0){ ln[++nlog]=log(q[n]); cl[nlog]=c[n]; Sxl+=ln[nlog]; Syl+=cl[nlog]; Sx2l+=ln[nlog]*ln[nlog]; Sxyl+=ln[nlog]*cl[nlog]; } }
END{
  a=0;b=0; if(n>1){den=n*Sxx - Sx*Sx; if(den!=0){b=(n*Sxy - Sx*Sy)/den; a=(Sy - b*Sx)/n} }
  al=0;bl=0; if(nlog>1){denl=nlog*Sx2l - Sxl*Sxl; if(denl!=0){bl=(nlog*Sxyl - Sxl*Syl)/denl; al=(Syl - bl*Sxl)/nlog} }
  printf("{\"n\":%d,\"n_log\":%d,\"linear\":{\"a\":%.17g,\"b\":%.17g},\"loglinear\":{\"a\":%.17g,\"b\":%.17g}}\n",n,nlog,a,b,al,bl) > J
  print "#k","q","corr","pred_lin","pred_log","res_lin","res_log" > R
  for(i=1;i<=n;i++){ pl=a + b*q[i]; if(q[i]>0){plg=al + bl*log(q[i]); rlg=c[i]-plg;} else {plg=""; rlg="";} rl=c[i]-pl; print k[i],q[i],c[i],pl,plg,rl,rlg >> R }
}' "$IN"
echo "[fit] wrote $OUT_JSON and $OUT_RES"
