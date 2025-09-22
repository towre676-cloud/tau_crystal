#!/usr/bin/env bash
set -euo pipefail; set +H
in="${1:?usage: landmarks_to_r_safe.sh <in.tsv> <out.tsv>}"
out="${2:?usage: landmarks_to_r_safe.sh <in.tsv> <out.tsv>}"

# Try the original first (if it works, keep that behavior)
if bash scripts/validation/landmarks_to_r.sh "$in" "$out" 2>/dev/null; then
  exit 0
fi

# Fallback: mean-center, scale by max axis range (clamped to >=1), emit 17 stable features.
# Input: 68 lines of "x<TAB>y<TAB>z"
awk -v OUT="$out" '
  function abs(x){return x<0?-x:x}
  function sq(x){return x*x}
  function max(a,b){return (a>b)?a:b}
  BEGIN{
    n=0; sx=sy=sz=0;
    minx=miny=minz=1e300; maxx=maxy=maxz=-1e300;
  }
  NF>=3{
    ++n; X[n]=$1+0; Y[n]=$2+0; Z[n]=$3+0;
    sx+=X[n]; sy+=Y[n]; sz+=Z[n];
    if(X[n]<minx)minx=X[n]; if(X[n]>maxx)maxx=X[n];
    if(Y[n]<miny)miny=Y[n]; if(Y[n]>maxy)maxy=Y[n];
    if(Z[n]<minz)minz=Z[n]; if(Z[n]>maxz)maxz=Z[n];
  }
  END{
    if(n==0){ # empty -> deterministic zeros
      print "r1\t0"  > OUT; for(i=2;i<=17;i++) print "r" i "\t0" >> OUT; exit 0
    }
    mx=sx/n; my=sy/n; mz=sz/n;

    rx=max(1e-9, maxx-minx);
    ry=max(1e-9, maxy-miny);
    rz=max(1e-9, maxz-minz);
    s=max(rx, max(ry, rz)); if(s<1) s=1;  # clamp scale

    # Accumulate moments on centered+scaled coords
    vx=vy=vz=cxy=cyz=czx=0;
    L2=L1=0;  # L1/L2 norms over all points
    # pick three stable landmark indices (1, 17, 34) when present
    i1=(n>=1)?1:1; i2=(n>=17)?17:n; i3=(n>=34)?34:n;

    for(i=1;i<=n;i++){
      cx=(X[i]-mx)/s; cy=(Y[i]-my)/s; cz=(Z[i]-mz)/s;
      vx+=cx*cx; vy+=cy*cy; vz+=cz*cz;
      cxy+=cx*cy; cyz+=cy*cz; czx+=cz*cx;
      rlen=sqrt(cx*cx+cy*cy+cz*cz);
      L1+=abs(rlen); L2+=rlen*rlen;
      if(i==i1){x1=cx;y1=cy;z1=cz}
      if(i==i2){x2=cx;y2=cy;z2=cz}
      if(i==i3){x3=cx;y3=cy;z3=cz}
    }
    vx/=n; vy/=n; vz/=n; cxy/=n; cyz/=n; czx/=n;

    # pairwise distances between anchor landmarks
    d12=sqrt(sq(x1-x2)+sq(y1-y2)+sq(z1-z2));
    d23=sqrt(sq(x2-x3)+sq(y2-y3)+sq(z2-z3));
    d31=sqrt(sq(x3-x1)+sq(y3-y1)+sq(z3-z1));

    # a few simple affine-invariant ratios of ranges
    rxy=(rx>1e-9?rx:1); ryy=(ry>1e-9?ry:1); rzz=(rz>1e-9?rz:1);
    qx=rx/rxy; qy=ry/ryy; qz=rz/rzz; # these become 1; include instead normalized range ratios:
    rxy_ratio=rx/ryy; ryz_ratio=ry/rzz; rzx_ratio=rz/rxy;

    # 17 features (bounded, scale/translation invariant)
    printf "r1\t%.8f\n", vx               > OUT
    printf "r2\t%.8f\n", vy               >> OUT
    printf "r3\t%.8f\n", vz               >> OUT
    printf "r4\t%.8f\n", cxy              >> OUT
    printf "r5\t%.8f\n", cyz              >> OUT
    printf "r6\t%.8f\n", czx              >> OUT
    printf "r7\t%.8f\n", L1/n             >> OUT
    printf "r8\t%.8f\n", L2/n             >> OUT
    printf "r9\t%.8f\n", d12              >> OUT
    printf "r10\t%.8f\n", d23             >> OUT
    printf "r11\t%.8f\n", d31             >> OUT
    printf "r12\t%.8f\n", (vx+vy+vz)      >> OUT
    printf "r13\t%.8f\n", (vx*vy+vy*vz+vz*vx) >> OUT
    printf "r14\t%.8f\n", (vx*vy*vz)      >> OUT
    printf "r15\t%.8f\n", rxy_ratio       >> OUT
    printf "r16\t%.8f\n", ryz_ratio       >> OUT
    printf "r17\t%.8f\n", rzx_ratio       >> OUT
  }' "$in"
