#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
src="analysis/bash_theta_scan.tsv"; out="analysis/morse_crit.tsv"; svg="analysis/plots/morse.svg"
[ -s "$src" ] || { echo "[skip] $src not found"; exit 0; }
: > "$out"
printf "%s\n" "S_micro\tT_micro\tdiff\tclass" >> "$out"
tmp="$(mktemp)"; cp "$src" "$tmp"
awk 'NR==1{next} {s=$1;t=$2;d=$3;key=s FS t; D[key]=d; S[s]=1; T[t]=1} END{for (si in S) ss[++iS]=si; for (ti in T) tt[++iT]=ti; nS=iS; nT=iT; # sort
  asort(ss); asort(tt);
  for (i=1;i<=nS;i++) for (j=1;j<=nT;j++){
    s=ss[i]; t=tt[j]; key=s FS t; d=D[key]; if(d=="") continue;
    kU=s FS tt[j-1]; kD=s FS tt[j+1]; kL=ss[i-1] FS t; kR=ss[i+1] FS t;
    du=(D[kU]==""?d:D[kU]); dd=(D[kD]==""?d:D[kD]); dl=(D[kL]==""?d:D[kL]); dr=(D[kR]==""?d:D[kR]);
    gu=du-d; gd=dd-d; gl=dl-d; gr=dr-d;
    # 2D discrete Hessian signature via sign pattern of neighbors
    wors=0; bett=0;
    if(du>d) wors++; else if(du<d) bett++;
    if(dd>d) wors++; else if(dd<d) bett++;
    if(dl>d) wors++; else if(dl<d) bett++;
    if(dr>d) wors++; else if(dr<d) bett++;
    cls="saddle";
    if(wors==4) cls="min";
    else if(bett==4) cls="max";
    print s "\t" t "\t" d "\t" cls;
  }}' "$tmp" >> "$out"
rm -f "$tmp"
: > "$svg"
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1200\" height=\"800\">" >> "$svg"
printf "%s\n" "<rect x=\"0\" y=\"0\" width=\"1200\" height=\"800\" fill=\"white\"/>" >> "$svg"
awk -v W=1100 -v H=700 'NR==1{next} {S[$1]=1; T[$2]=1} END{i=0; for(k in S) xs[++i]=k; asort(xs); j=0; for(k in T) ys[++j]=k; asort(ys); for(i=1;i<=length(xs);i++) xmap[xs[i]]=50+(i-1)*(W/(length(xs)>1?length(xs)-1:1)); for(j=1;j<=length(ys);j++) ymap[ys[j]]=750-(j-1)*(H/(length(ys)>1?length(ys)-1:1)); }" "$out" > /dev/null
awk -v W=1100 -v H=700 'NR==1{next} {S[$1]=1; T[$2]=1} END{i=0; for(k in S) xs[++i]=k; asort(xs); j=0; for(k in T) ys[++j]=k; asort(ys); for(i=1;i<=length(xs);i++) xmap[xs[i]]=50+(i-1)*(W/(length(xs)>1?length(xs)-1:1)); for(j=1;j<=length(ys);j++) ymap[ys[j]]=750-(j-1)*(H/(length(ys)>1?length(ys)-1:1)); }' "$out" 1>/dev/null 2>&1
awk 'BEGIN{print ""}' >/dev/null 2>&1
awk -v OFS="\t" -v W=1100 -v H=700 -v o="$svg" 'NR==FNR && NR>1 {S[$1]=1; T[$2]=1; next}
  NR>FNR && FNR==1 {next}
  NR==FNR {next}
' "$out" "$out" >/dev/null 2>&1
awk -v svg="$svg" -v W=1100 -v H=700 '
  NR==FNR && NR>1 {S[$1]=1; T[$2]=1; next}
  END{}
' "$out" "$out" >/dev/null 2>&1
awk -v svg="$svg" 'NR==1{next} {s=$1;t=$2;d=$3;c=$4;Ss[s]=1;Tt[t]=1; Ds=(s<minS||minS==""?minS=s:minS); Dt=(t<minT||minT==""?minT=t:minT); if(s>maxS) maxS=s; if(t>maxT) maxT=t; rows[NR]=$0}
END{
  W=1100; H=700; x0=50; y0=50;
  for(i=2;i<=NR;i++){
    split(rows[i],a,"\t"); s=a[1]; t=a[2]; d=a[3]; c=a[4];
    xs=(maxS==minS?0.5: (s-minS)/(maxS-minS)); ys=(maxT==minT?0.5: (t-minT)/(maxT-minT));
    X=int(x0 + xs*W); Y=int(750 - ys*H);
    col="#000000"; r=3;
    if(c=="min"){ col="#008000"; r=5 }
    else if(c=="max"){ col="#b00000"; r=5 }
    else if(c=="saddle"){ col="#ff9900"; r=4 }
    print "<circle cx=\"" X "\" cy=\"" Y "\" r=\"" r "\" fill=\"" col "\"/>" >> svg
  }
}' "$out"
printf "%s\n" "</svg>" >> "$svg"
