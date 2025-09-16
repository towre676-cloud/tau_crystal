#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/satake_angles.tsv"; svg="analysis/plots/satake_polar.svg"
mkdir -p analysis analysis/plots
if ! command -v jq >/dev/null 2>&1; then echo "[satake] jq not found"; : > "$out"; : > "$svg"; exit 0; fi
jq -r '.hecke_eigenvalues | to_entries[] | "\(.key) \(.value)"' "$in" |
awk 'function atan2(y,x){return x>0?atan(y/x):(x<0?atan(y/x)+3.141592653589793:(y>0?1.5707963267948966:-1.5707963267948966))} {p=$1; ap=$2; twoSqrtP=2*sqrt(p); if(twoSqrtP==0)next; c=ap/twoSqrtP; if(c>1)c=1; if(c<-1)c=-1; theta=atan2(sqrt(1-c*c),c); bin=int(theta*8/3.141592653589793); if(bin<0)bin=0; if(bin>7)bin=7; cnt[bin]++; ang[bin]=bin*3.141592653589793/8} END{for(b=0;b<8;b++) printf "%d\t%d\t%f\n", b, cnt[b]+0, ang[b]+0}' > "$out"
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 400 400\"><g transform=\"translate(200,200)\">" > "$svg"
awk 'function max(a,b){return a>b?a:b} function cosd(r){return cos(r)} function sind(r){return sin(r)} {m=max(m,$2)} END{if(m==0)m=1}' "$out" >/dev/null 2>&1
awk '{mx=(mx>$2?mx:$2)} END{if(mx==0)mx=1} {ang=$3; r=150*($2/mx*0.8+0.2); dx=r*cos(ang); dy=r*sin(ang); printf "<path d=\\"M 0,0 L %f,%f A %d,%d 0 0,1 %f,%f Z\\" fill=\\"#4e79a7\\" opacity=\\"0.85\\"/>\n",dx,dy,150,150,-dx,-dy}' "$out" >> "$svg"
printf "%s\n" "</g></svg>" >> "$svg"
echo "[satake] wrote $out and $svg"
