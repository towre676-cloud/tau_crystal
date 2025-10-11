#!/usr/bin/env sh
# Usage: ./lrc_annotate.sh input.csv > annotated.csv
# Adds: thr_num,thr_den,slack_num,slack_den,hits_bound,wt_ok

CSV="${1:-lrc_random_results.csv}"
awk -F, '
function gcd(a,b){a=(a<0?-a:a);b=(b<0?-b:b);while(b){t=a%b;a=b;b=t}return a}
function reduce(n,d,  g){g=gcd(n,d); if(g==0){return} n/=g; d/=g; return n":"d}
function cmp_frac(n1,d1,n2,d2){ # returns -1/0/1 for n1/d1 vs n2/d2
  x=n1*d2 - n2*d1; return (x<0?-1:(x>0?1:0))
}
BEGIN{
  OFS=","
  print "N,k,a_list,s_num,s_den,max_num,max_den,OK,thr_num,thr_den,slack_num,slack_den,hits_bound,wt_ok"
}
NR==1 { next }
{
  N=$1; k=$2; alist=$3; sN=$4; sD=$5; mN=$6; mD=$7; ok=$8
  thrN=1; thrD=k+1

  # slack = max - 1/(k+1)
  num = mN*thrD - mD*thrN
  den = mD*thrD
  # normalise sign
  if(den<0){den=-den; num=-num}
  # reduce
  split(reduce(num,den),R,":"); if(R[1]!=""){sn=R[1]; sd=R[2]} else {sn=num; sd=den}

  hits = (sn==0 ? "YES":"NO")

  # verify witness: compute min_i dist(a_i * s mod 1)
  wt_ok="UNKNOWN"
  if(sD>0){
    # strip quotes and split a_list
    gsub(/"/,"",alist); gsub(/^ +| +$/,"",alist)
    nsplit=split(alist, A, /[[:space:]]+/)
    minN=-1; minD=sD
    for(i=1;i<=nsplit;i++){
      ai=A[i]+0
      r = (ai*sN) % sD
      if(r<0) r+=sD
      dn = r
      if(dn*2 > sD) dn = sD - dn
      # reduce dn/sD
      g = gcd(dn,sD); dn/=g; dd=sD/g
      if(minN<0 || cmp_frac(dn,dd,minN,minD)<0){minN=dn; minD=dd}
    }
    wt_ok = (cmp_frac(minN,minD,mN,mD)==0 ? "YES":"NO")
  }

  print N,k,$3,sN,sD,mN,mD,ok,thrN,thrD,sn,sd,hits,wt_ok
}' "$CSV"
