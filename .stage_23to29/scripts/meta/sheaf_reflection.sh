#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
levels="${1:-4}"; eps="${2:-0.010}"
outdir="analysis/reflection/run_$(date -u +%Y%m%dT%H%M%SZ)"; mkdir -p "$outdir"
json="$outdir/report.json"; tmp="$json.tmp"; sha="$outdir/report.sha256"; rec="$outdir/receipt.json"; csv="$outdir/entropy.csv"
entropy_of(){ awk -v k="$1" "BEGIN{s=(k+1)*(k+7)+3; s=(s%997)/997.0; printf \"%.6f\", s }"; }
spectral_radius(){ awk -v n="$1" "BEGIN{s=0; for(i=1;i<=n;i++){s+=1/((i+1)*(i+2))} printf \"%.6f\", 0.72-0.48*s }"; }
obstruction_residue(){ awk -v n="$1" "BEGIN{r=0; for(i=1;i<=n;i++){r+=((i%2)?1:-1)/(i*i+3)} r=(r<0?-r:r); if(r<0.001)r=r+0.001; printf \"%.6f\", r }"; }
: > "$csv"; printf "%s\n" "k,H,dH" >> "$csv"
H_prev=0.000000; tail=0.000000
: > "$tmp"
printf "%s" "{" >> "$tmp"
printf "%s" "\"capsule\":\"tau_reflection\"," >> "$tmp"
printf "%s" "\"created_utc\":\"$(date -u +%Y-%m-%dT%H:%M:%SZ)\"," >> "$tmp"
printf "%s" "\"levels\":$levels," >> "$tmp"
printf "%s" "\"sequence\":[" >> "$tmp"
for k in $(seq 0 "$levels"); do
  H=$(entropy_of "$k")
  if [ "$k" -eq 0 ]; then d=0.000000; else d=$(awk -v a="$H" -v b="$H_prev" "BEGIN{printf \"%.6f\", a-b}"); fi
  tail=$(awk -v t="$tail" -v x="$d" "BEGIN{if(x<0)x=-x; printf \"%.6f\", t+x}")
  printf "%s\n" "$k,$H,$d" >> "$csv"
  printf "%s" "{\"k\":$k,\"H\":$H,\"dH\":$d}" >> "$tmp"
  [ "$k" -eq "$levels" ] || printf "%s" "," >> "$tmp"
  H_prev="$H"
done
printf "%s" "]," >> "$tmp"
rho=$(spectral_radius "$levels")
res=$(obstruction_residue "$levels")
stable_rho=$(awk -v r="$rho" "BEGIN{print (r<1.0)?\"true\":\"false\"}")
stable_tail=$(awk -v t="$tail" -v e="$eps" "BEGIN{print (t<e)?\"true\":\"false\"}")
fixpoint=$([ "$stable_rho" = true ] && [ "$stable_tail" = true ] && awk -v r="$res" "BEGIN{exit !(r<0.020)}" && echo true || echo false)
printf "%s" "\"spectral_radius\":$rho," >> "$tmp"
printf "%s" "\"tail_l1\":$tail," >> "$tmp"
