#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_dual_from_a.sh <in.tsv> <out.tsv>}"
OUT="${2:?}"
# normalize CRLF (harmless elsewhere)
sed -i 's/\r$//' "$IN" 2>/dev/null || true

tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
# sort numerically by u, keep header
{ IFS= read -r H; printf '%s\n' "$H"; sort -t$'\t' -k1,1g; } < "$IN" > "$tmp"

awk -v OFS='\t' '
function find(name,   i){name=tolower(name); for(i=1;i<=NF;i++){t=$i; gsub(/[^A-Za-z0-9_]+/,"_",t); t=tolower(t); if(t==name) return i} return -1}
NR==1{
  iu=find("u"); ia=find("a"); ia1=find("a1"); ia2=find("a2"); ip2=find("p2"); ip1=find("p1"); ip0=find("p0")
  if(iu<0||ia<0||ia1<0||ia2<0||ip2<0||ip1<0||ip0<0){ print "ERROR: missing column(s) u,a,a1,a2,p2,p1,p0" > "/dev/stderr"; exit 2 }
  print $0; next
}
NR==2{
  u  =$iu+0.0; a =$ia+0.0; a1=$ia1+0.0; a2=$ia2+0.0; p2=$ip2+0.0; p1=$ip1+0.0
  P  =(p2!=0? p1/p2 : 0.0)
  H  = 1.0                 # choose H(u1)=1
  G  = 0.0                 # v(u1)=0
  v  = G
  vp = (a!=0 ? H/(a*a) : 0.0)
  vpp= (a!=0 ? H*( -P/(a*a) - 2.0*a1/(a*a*a) ) : 0.0)
  aD  = a*v
  aD1 = a1*v + a*vp
  aD2 = a2*v + 2.0*a1*vp + a*vpp
  $ia=aD; $ia1=aD1; $ia2=aD2
  print $0
  up=u; ap=a; a1p=a1; Pp=P; Hp=H; Gp=G
  next
}
{
  u  =$iu+0.0; a =$ia+0.0; a1=$ia1+0.0; a2=$ia2+0.0; p2=$ip2+0.0; p1=$ip1+0.0
  P  =(p2!=0? p1/p2 : 0.0)
  du = u - up
  # trapezoid on ln H: lnH += -∫P du
  H  = Hp * exp( -0.5*(P+Pp)*du )
  # trapezoid on G = ∫ H / a^2 du
  term  = (a !=0 ? H /(a*a)  : 0.0)
  termp = (ap!=0 ? Hp/(ap*ap) : 0.0)
  G  = Gp + 0.5*(term+termp)*du
  v  = G
  vp = term
  vpp= (a!=0 ? H*( -P/(a*a) - 2.0*a1/(a*a*a) ) : 0.0)
  aD  = a*v
  aD1 = a1*v + a*vp
  aD2 = a2*v + 2.0*a1*vp + a*vpp
  $ia=aD; $ia1=aD1; $ia2=aD2
  print $0
  up=u; ap=a; a1p=a1; Pp=P; Hp=H; Gp=G
}
' "$tmp" > "$OUT"
