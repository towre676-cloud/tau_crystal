#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
SCAN="analysis/bash_theta_scan.tsv"; MORSE="analysis/morse_crit.tsv"; OUT="analysis/basins.tsv"; SVG="analysis/plots/basins.svg"
[ -s "$SCAN" ] && [ -s "$MORSE" ] || { echo "[basins] skip: need $SCAN and $MORSE"; exit 0; }
: > "$OUT"; printf "%s\n" "S_micro\tT_micro\tdiff\tbasin" >> "$OUT"
awk -F"\t" 'FNR==NR{if(NR>1 && $4=="min"){m++; MS[m]=$1; MT[m]=$2} next} NR>1{best=0;bd=0; for(i=1;i<=m;i++){ds=$1-MS[i]; if(ds<0)ds=-ds; dt=$2-MT[i]; if(dt<0)dt=-dt; d=ds*ds+dt*dt; if(best==0||d<bd){best=i;bd=d}} print $1 "\t" $2 "\t" $3 "\t" (m?best:0)}' "$MORSE" "$SCAN" >> "$OUT"
: > "$SVG"; printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1200\" height=\"800\"><rect width=\"1200\" height=\"800\" fill=\"white\"/>" >> "$SVG"
awk -F"\t" 'NR==1{next} {S[NR]=$1; T[NR]=$2; B[NR]=$4; if(minS==""||$1<minS)minS=$1; if($1>maxS)maxS=$1; if(minT==""||$2<minT)minT=$2; if($2>maxT)maxT=$2; if($4>maxB)maxB=$4} END{for(i=2;i<=NR;i++){s=S[i];t=T[i];b=B[i]; xs=(maxS==minS?0.5:(s-minS)/(maxS-minS)); ys=(maxT==minT?0.5:(t-minT)/(maxT-minT)); X=int(50+xs*1100); Y=int(750-ys*700); # palette
  c=b%8; col="#000000"; if(c==1)col="#1f77b4"; else if(c==2)col="#2ca02c"; else if(c==3)col="#d62728"; else if(c==4)col="#9467bd"; else if(c==5)col="#8c564b"; else if(c==6)col="#e377c2"; else if(c==7)col="#7f7f7f"; else col="#bcbd22";
  print "<circle cx=\"" X "\" cy=\"" Y "\" r=\"3\" fill=\"" col "\" fill-opacity=\"0.7\"/>"}}' "$OUT" >> "$SVG"
printf "%s\n" "</svg>" >> "$SVG"; echo "[basins] wrote $OUT and $SVG"
