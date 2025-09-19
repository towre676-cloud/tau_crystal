#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
IN="${1:-analysis/bash_theta_scan.tsv}"
OUT="analysis/morse_crit.tsv"

# Build grid and detect minima
awk -F'\t' -v OFS='\t' '
NR==1 { next }
{
  S=$1+0; T=$2+0; D=$3+0
  key=S","T
  V[key]=D
  Svals[S]=1; Tvals[T]=1
  order[++n]=key
  byT[T]=byT[T] " " S
}
END{
  # derive minimal steps
  stepS=0; stepT=0
  for(t in Tvals){
    split(byT[t], arr, " ")
    prev=""
    for(i=1;i<=length(arr);i++){
      s=arr[i]+0; if(s==0 && arr[i]!="0") continue
      if(prev!=""){
        d=s-prev; if(d>0 && (stepS==0 || d<stepS)) stepS=d
      }
      prev=s
    }
  }
  # stepT via sorted unique values
  i=0; for(t in Tvals){ Ts[++i]=t+0 }
  # simple insertion sort (small sets)
  for(i2=2;i2<=i;i2++){ x=Ts[i2]; j=i2-1; while(j>=1 && Ts[j]>x){ Ts[j+1]=Ts[j]; j-- } Ts[j+1]=x }
  for(k=2;k<=i;k++){
    d=Ts[k]-Ts[k-1]; if(d>0 && (stepT==0 || d<stepT)) stepT=d
  }

  print "S_micro","T_micro","type","Delta","Hess_det"
  for(u=1;u<=n;u++){
    split(order[u], p, ","); s=p[1]+0; t=p[2]+0; d=V[order[u]]
    # neighbors (8)
    any=0; less=0
    for(dx=-1;dx<=1;dx++){
      for(dy=-1;dy<=1;dy++){
        if(dx==0 && dy==0) continue
        k=(s+dx*stepS)","(t+dy*stepT)
        if(k in V){ any=1; if(V[k] < d) less=1 }
      }
    }
    if(any && !less){
      fx2=0; fy2=0
      k1=(s-stepS)","t; k2=(s+stepS)","t
      if((k1 in V) && (k2 in V)) fx2 = V[k1] + V[k2] - 2*d
      k3=s","(t-stepT); k4=s","(t+stepT)
      if((k3 in V) && (k4 in V)) fy2 = V[k3] + V[k4] - 2*d
      print s,t,"minimum",d,fx2*fy2
    }
  }
}' "$IN" > "$OUT"

echo "[morse2d] minima: $(awk -F'\t' '$3~/^min/{c++} END{print (c?c:0)}' "$OUT") ; wrote $OUT and analysis/plots/morse.svg (if your plotter step runs)"
