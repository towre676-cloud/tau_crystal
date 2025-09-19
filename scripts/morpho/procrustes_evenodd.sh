#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
csv="${1:-}"; out="${2:-.tau_ledger/morpho/procrustes.local}"
[ -n "$csv" ] && [ -f "$csv" ] || { echo "missing csv" >&2; exit 2; }
mkdir -p "$(dirname "$out")"
h=$(sha256sum "$csv" | awk "{print \$1}")
tmp_evenodd="$out.tmp.eo"
awk -F, '
function trim(s){gsub(/^[[:space:]]+|[[:space:]]+$/,"",s);return s}
function isnum(s){return (s ~ /^-?[0-9]+(\.[0-9]+)?$/)}
NR==FNR{
  sub(/\r$/,"");
  for(i=1;i<=NF;i++) $i=trim($i);
  if(NF<4) next;
  if(isnum($1)&&isnum($2)&&isnum($3)&&isnum($4)){
    lx+=$1; ly+=$2; rx+=$3; ry+=$4; n++
  }
  next
}
FNR==1{
  if(n<3){ print "N=0"; exit 3 }
  Lcx=lx/n; Lcy=ly/n; Rcx=rx/n; Rcy=ry/n;
}
{
  sub(/\r$/,"");
  for(i=1;i<=NF;i++) $i=trim($i);
  if(NF<4) next;
  if(isnum($1)&&isnum($2)&&isnum($3)&&isnum($4)){
    lx0=$1-Lcx; ly0=$2-Lcy; rx0=$3-Rcx; ry0=$4-Rcy;
    mx=-rx0; my=ry0;
    ex=(lx0+mx)/2; ey=(ly0+my)/2;
    ox=(lx0-mx);  oy=(ly0-my);
    even+=ex*ex+ey*ey; odd+=ox*ox+oy*oy;
  }
}
END{
  if(n<3){ exit 3 }
  tot=even+odd; H=(tot>0? even/tot : 0);
  printf("EVEN=%.8f\nODD=%.8f\nH=%.8f\n",even,odd,H);
}
' "$csv" "$csv" > "$tmp_evenodd" || { echo "procrustes: invalid or insufficient rows" >&2; exit 4; }
ts=$(date -u +%Y%m%dT%H%M%SZ)
: > "$out"
printf "MOD=%s\n"    "procrustes" >> "$out"
printf "SRC=%s\n"    "$csv"       >> "$out"
printf "SHA256=%s\n" "$h"         >> "$out"
cat "$tmp_evenodd"                 >> "$out"
printf "TIME=%s\n"   "$ts"         >> "$out"
rm -f "$tmp_evenodd"; echo "ok: procrustes -> $out"
