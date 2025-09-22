#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
awk -F"\t|,| " '{if($1!=""){sx+=$1; sy+=$2; sz+=$3; n++}} END{cx=sx/n; cy=sy/n; cz=sz/n; print cx"\t"cy"\t"cz}' "$IN" > /tmp/ctr.$$
read CX CY CZ < /tmp/ctr.$$
awk -F"\t|,| " -v cx="$CX" -v cy="$CY" -v cz="$CZ" '{if($1!=""){x=$1-cx;y=$2-cy;z=$3-cz; printf("%.9f\t%.9f\t%.9f\n",x,y,z)}}' "$IN" > /tmp/cent.$$
awk -F"\t" 'NR<=20{t+=($1*$1+$2*$2+$3*$3)} END{s=sqrt(t/(NR?NR:1)); if(s==0)s=1; print s}' /tmp/cent.$$ > /tmp/scale.$$
read SC < /tmp/scale.$$
awk -F"\t" -v s="$SC" '{printf("%.9f\t%.9f\t%.9f\n",$1/s,$2/s,$3/s)}' /tmp/cent.$$ > /tmp/norm.$$
awk -F"\t" 'BEGIN{for(i=1;i<=3;i++)a[i]=0} {a[1]+=$1; a[2]+=$2; a[3]+=$3; n++} END{printf("%.9f\t%.9f\t%.9f\n",a[1]/n,a[2]/n,a[3]/n)}' /tmp/norm.$$ > /tmp/f1.$$
printf "%s\n" 1 5 9 13 17 21 25 > /tmp/idx.$$
> /tmp/dots.$$; while read -r idx; do
  awk -F"\t" -v id="$idx" 'NR==id{ax=$1;ay=$2;az=$3} END{print ax"\t"ay"\t"az}' /tmp/norm.$$ > /tmp/a.$$
  read AX AY AZ < /tmp/a.$$
  awk -F"\t" -v ax="$AX" -v ay="$AY" -v az="$AZ" '{d=$1*ax+$2*ay+$3*az; s+=d; c++} END{printf("%.9f\n",s/c)}' /tmp/norm.$$ >> /tmp/dots.$$
done < /tmp/idx.$$
paste -d"\t" /tmp/f1.$$ /tmp/dots.$$ > /tmp/raw17.$$
awk -F"\t" 'function rat(x,   a,b,g,t){a=int(x*10000+0.5); b=10000; g=a<0?-a:a; while(b&&g){t=g%b; g=b; b=t} if(g==0)g=1; a=int(x*10000+0.5); b=10000; a=int(a/g); b=int(10000/g); return a"/"b} {out=""; for(i=1;i<=NF;i++){if(i>1)out=out"\t"; out=out rat($i)} print out}' /tmp/raw17.$$ > "$OUT"
rm -f /tmp/ctr.$$ /tmp/cent.$$ /tmp/scale.$$ /tmp/norm.$$ /tmp/f1.$$ /tmp/idx.$$ /tmp/a.$$ /tmp/dots.$$ /tmp/raw17.$$
