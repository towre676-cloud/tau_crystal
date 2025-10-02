#!/usr/bin/env bash
set -euo pipefail; set +H
in="${1:?usage: pre_normalize.sh <in.tsv> <out.tsv>}"
out="${2:?usage: pre_normalize.sh <in.tsv> <out.tsv>}"
# 68 lines of x<TAB>y<TAB>z → mean-center, scale by max axis-range (fallback 1)
awk '
  function abs(x){return x<0?-x:x}
  BEGIN{minx=miny=minz=1e300; maxx=maxy=maxz=-1e300}
  NF>=3{
    x[NR]=$1; y[NR]=$2; z[NR]=$3;
    sx+=$1; sy+=$2; sz+=$3;
    if($1<minx)minx=$1; if($1>maxx)maxx=$1;
    if($2<miny)miny=$2; if($2>maxy)maxy=$2;
    if($3<minz)minz=$3; if($3>maxz)maxz=$3;
    n=NR
  }
  END{
    if(n==0){ exit 1 }
    mx=sx/n; my=sy/n; mz=sz/n;
    rx=maxx-minx; ry=maxy-miny; rz=maxz-minz;
    s=rx; if(ry>s)s=ry; if(rz>s)s=rz;
    if(s<=0) s=1;               # hard guard: avoid zero scale
    for(i=1;i<=n;i++){
      printf("%.10f\t%.10f\t%.10f\n", (x[i]-mx)/s, (y[i]-my)/s, (z[i]-mz)/s)
    }
  }
' "$in" > "$out"
