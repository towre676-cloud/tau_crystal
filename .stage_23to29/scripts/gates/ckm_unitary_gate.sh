#!/usr/bin/env bash
set -euo pipefail; umask 022
f="${1:-analysis/fermion/ckm.tsv}"
tol=${CKM_TOL:-1e-6}
allow=${ALLOW_PLACEHOLDER:-0}
[ -f "$f" ] || { echo "[CKM] missing $f"; exit 2; }

# placeholder detection
if head -n1 "$f" | grep -qi 'placeholder CKM'; then
  if [ "$allow" = "1" ]; then
    echo "[CKM] placeholder allowed (ALLOW_PLACEHOLDER=1)"; exit 0
  else
    echo "[CKM] placeholder present; failing until real fit lands"; exit 2
  fi
fi

awk -v tol="$tol" '
function abs(x){return x<0?-x:x}
function isn(x){return (x ~ /^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/)}
function near(x,y){return abs(x-y)<=tol}
BEGIN{rows=0}
{
  n=split($0,a,/[ \t]+/)
  rowc=0
  for(i=1;i<=n;i++){ if(isn(a[i])){ rowc++; row[rowc]=a[i]+0 } else { if(rowc==0) rowc=0; break } }
  if(rowc>=3){ for(j=1;j<=3;j++) m[rows,j]=row[j]; rows++ }
}
END{
  if(rows<3){print "[CKM] need 3 numeric rows with 3 columns"; exit 3}
  ok=1
  for(c=1;c<=3;c++){ s=0; for(r=0;r<3;r++) s+=m[r,c]*m[r,c]; if(!near(s,1)){printf("[CKM] col %d norm^2=%g\n",c,s); ok=0}}
  for(c1=1;c1<=3;c1++) for(c2=c1+1;c2<=3;c2++){ dot=0; for(r=0;r<3;r++) dot+=m[r,c1]*m[r,c2]; if(!(abs(dot)<=tol)){printf("[CKM] cols %d,%d dot=%g\n",c1,c2,dot); ok=0}}
  if(ok){print "[CKM] ok unitary within tol=" tol; exit 0} else exit 1
}' "$f"
