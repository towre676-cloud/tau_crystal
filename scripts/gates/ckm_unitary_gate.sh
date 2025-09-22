#!/usr/bin/env bash
set -euo pipefail; umask 022
f="${1:-analysis/fermion/ckm.tsv}"
tol=${CKM_TOL:-1e-6}
[ -f "$f" ] || { echo "[CKM] missing $f"; exit 2; }
rc=0
awk -v tol="$tol" '
function abs(x){return x<0?-x:x}
function isn(x){return (x ~ /^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/)}
function near(x,y){return abs(x-y)<=tol}
BEGIN{rows=0}
{
  # split on tabs/spaces
  n=split($0, a, /[ \t]+/)
  # build a numeric row from leading fields
  rowc=0
  for(i=1;i<=n;i++){
    if(isn(a[i])){ rowc++; row[rowc]=a[i]+0 } else { # stop at first non-numeric cell (header label etc.)
      if(rowc==0){ rowc=0; } # header line, ignore entirely
      break
    }
  }
  if(rowc>=3){
    for(j=1;j<=3;j++) m[rows,j]=row[j]
    rows++
  }
}
END{
  if(rows<3){print "[CKM] need 3 numeric rows with 3 columns"; exit 3}
  # column norms
  ok=1
  for(c=1;c<=3;c++){
    s=0; for(r=0;r<3;r++){s+=m[r,c]*m[r,c]}
    if(!near(s,1)){printf("[CKM] col %d norm^2=%g\n",c,s); ok=0}
  }
  # orthogonality
  for(c1=1;c1<=3;c1++) for(c2=c1+1;c2<=3;c2++){
    dot=0; for(r=0;r<3;r++){dot+=m[r,c1]*m[r,c2]}
    if(!(abs(dot)<=tol)){printf("[CKM] cols %d,%d dot=%g\n",c1,c2,dot); ok=0}
  }
  if(ok){print "[CKM] ok unitary within tol=" tol; exit 0} else exit 1
}
' "$f" || rc=$?
exit ${rc:-0}
