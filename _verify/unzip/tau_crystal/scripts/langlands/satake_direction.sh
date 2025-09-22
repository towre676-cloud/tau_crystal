#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/satake_angles.tsv"; svg="analysis/plots/satake_polar.svg"
mkdir -p analysis analysis/plots
if ! command -v jq >/dev/null 2>&1; then echo "[satake] jq not found"; : > "$out"; : > "$svg"; exit 0; fi
if [ ! -s "$in" ] || ! jq -e 'has("hecke_eigenvalues") and (.hecke_eigenvalues|type=="object" and (.|length>0))' "$in" >/dev/null 2>&1; then
  echo "[satake] no hecke_eigenvalues in $in"; : > "$out"; : > "$svg"; exit 0
fi
jq -r '.hecke_eigenvalues | to_entries[] | "\(.key)\t\(.value)"' "$in" |
awk -F"\t" 'BEGIN{pi=3.141592653589793} {p=$1+0; ap=$2+0; t2=2*sqrt(p); if(t2<=0) next; c=ap/t2; if(c>1)c=1; if(c<-1)c=-1; s=sqrt(1-c*c); theta=atan2(s,c); bin=int(theta*8/pi); if(bin<0)bin=0; if(bin>7)bin=7; cnt[bin]++; ang[bin]=bin*pi/8} END{for(b=0;b<8;b++) printf "%d\t%d\t%f\n", b, (b in cnt?cnt[b]:0), (b in ang?ang[b]:b*pi/8)}' > "$out"
max=$(awk 'mx<$2{mx=$2}END{print mx+0}' "$out"); [ -z "$max" ] && max=1
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 400 400\"><g transform=\"translate(200,200)\">" > "$svg"
while IFS=$'\t' read -r b c ang; do
  r=$(awk -v c="$c" -v m="$max" 'BEGIN{if(m==0)m=1; print 150*((c/m)*0.8+0.2)}')
  dx=$(awk -v r="$r" -v a="$ang" 'BEGIN{print r*cos(a)}')
  dy=$(awk -v r="$r" -v a="$ang" 'BEGIN{print r*sin(a)}')
  ndx=$(awk -v x="$dx" 'BEGIN{print -x}')
  ndy=$(awk -v y="$dy" 'BEGIN{print -y}')
  printf "<path d=\\"M 0,0 L %s,%s A 150,150 0 0,1 %s,%s Z\\" fill=\\"#4e79a7\\" opacity=\\"0.85\\"/>\n" "$dx" "$dy" "$ndx" "$ndy" >> "$svg"
done < "$out"
printf "%s\n" "</g></svg>" >> "$svg"
echo "[satake] wrote $out and $svg"
