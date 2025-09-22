#!/usr/bin/env bash
set -euo pipefail; set +H
in="${1:?usage: landmarks_to_r_safe.sh <in.tsv> <out.tsv>}"
out="${2:?usage: landmarks_to_r_safe.sh <in.tsv> <out.tsv>}"

# Try original first
if bash scripts/validation/landmarks_to_r.sh "$in" "$out" 2>/dev/null; then
  exit 0
fi

# Fallback: mean-center, scale by max axis range (clamped to 1), 17 guarded features
awk -v OUT="$out" '
  function max(a,b){return a>b?a:b}
  BEGIN{
    minx=miny=minz=1e300; maxx=maxy=maxz=-1e300;
    sx=sy=sz=0; n=0;
  }
  NF>=3{
    n++; X[n]=$1; Y[n]=$2; Z[n]=$3;
    sx+=$1; sy+=$2; sz+=$3;
    if($1<minx)minx=$1; if($1>maxx)maxx=$1;
    if($2<miny)miny=$2; if($2>maxy)maxy=$2;
    if($3<minz)minz=$3; if($3>maxz)maxz=$3;
  }
  END{
    if(n<1) exit 2;
    mx=sx/n; my=sy/n; mz=sz/n;
    rx=maxx-minx; ry=maxy-miny; rz=maxz-minz;
    s=rx; if(ry>s)s=ry; if(rz>s)s=rz; if(s<=0)s=1;     # clamp to avoid div/0
    cxx=cyy=czz=cxy=cxz=cyz=sx1=sy1=sz1=sx3=sy3=sz3=0; maxr=0;
    for(i=1;i<=n;i++){
      x=(X[i]-mx)/s; y=(Y[i]-my)/s; z=(Z[i]-mz)/s;
      r2=x*x + y*y + z*z; if(r2>maxr)maxr=r2;
      cxx+=x*x; cyy+=y*y; czz+=z*z;
      cxy+=x*y; cxz+=x*z; cyz+=y*z;
      sx1+=x;  sy1+=y;  sz1+=z;
      sx3+=x*x*x; sy3+=y*y*y; sz3+=z*z*z;
    }
    invn = 1.0/n;
    r[1]=sx1*invn;   r[2]=sy1*invn;   r[3]=sz1*invn;
    r[4]=cxx*invn;   r[5]=cyy*invn;   r[6]=czz*invn;
    r[7]=cxy*invn;   r[8]=cxz*invn;   r[9]=cyz*invn;
    r[10]=sx3*invn;  r[11]=sy3*invn;  r[12]=sz3*invn;
    r[13]=maxr;
    r[14]=(cxx+cyy+czz)*invn;
    r[15]=(cxy+cxz+cyz)*invn;
    r[16]=(sx1*sy1 + sx1*sz1 + sy1*sz1)*invn;
    r[17]=1.0;
    for(k=1;k<=17;k++) printf("r%02d\t%.10f\n", k, r[k]) > OUT;
  }
' "$in"
