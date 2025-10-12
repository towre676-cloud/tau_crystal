#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_dual_pair.sh <in.tsv> <out.tsv>}"
OUT="${2:?}"
sed -i 's/\r$//' "$IN" 2>/dev/null || true
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
# sort numerically on u, preserve header
{ IFS= read -r H; printf '%s\n' "$H"; sort -t$'\t' -k1,1g; } < "$IN" > "$tmp"

awk -v OFS='\t' '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
function idx(name,i){name=canon(name); for(i=1;i<=NF;i++) if(canon($i)==name) return i; return -1}
NR==1{
  iu=idx("u"); ia=idx("a"); ia1=idx("a1"); ia2=idx("a2"); ip2=idx("p2"); ip1=idx("p1"); ip0=idx("p0"); iseed=idx("seed");
  if(iu<0||ia<0||ia1<0||ia2<0||ip2<0||ip1<0||ip0<0){ print "ERROR: missing u/a/a1/a2/p2/p1/p0" > "/dev/stderr"; exit 2 }
  printf "u\ta\ta1\ta2\taD\taD1\taD2\tp2\tp1\tp0"; if(iseed>0) printf "\tseed"; printf "\n"; next
}
{
  u=$iu+0; a=$ia+0; a1=$ia1+0; a2=$ia2+0; p2=$ip2+0; p1=$ip1+0; p0=$ip0+0; seed=(iseed>0?$iseed:"");

  # v' = 1/a^2 ; v'' = -2 a1/a^3 ; integrate v' with trapezoid
  vp  = (a!=0 ? 1.0/(a*a) : 0.0);
  vpp = (a!=0 ? -2.0*a1/((a*a)*a) : 0.0);
  if(NR==2){ v=0.0; } else { v += 0.5*(vp_prev+vp)*(u-u_prev); }

  aD  = a*v;
  aD1 = a1*v + a*vp;
  aD2 = a2*v + 2.0*a1*vp + a*vpp;

  printf "%.15g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g", \
         u, a, a1, a2, aD, aD1, aD2, p2, p1, p0;
  if(iseed>0) printf "\t%s", seed; printf "\n";

  u_prev=u; vp_prev=vp;
}
' "$tmp" > "$OUT"
