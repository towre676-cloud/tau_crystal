#!/usr/bin/env bash
set -euo pipefail; umask 022
f="analysis/fermion/ckm.tsv"
tol=${CKM_TOL:-1e-6}
[ -f "$f" ] || { echo "[CKM] missing $f"; exit 2; }
# Expect a 3x3 real matrix in TSV (header optional). Validate norms and orthogonality.
rc=0
awk -v tol="$tol" '
function abs(x){return x<0?-x:x}
function near(x,y){return abs(x-y)<=tol}
BEGIN{rows=0}
NR==1{
  # if header has non-numeric, skip; detect with first field
  if ($1+0!=$1) {next}
}
{
  # numeric row
  for(i=1;i<=NF;i++){m[rows,i]=$i+0}
  rows++
}
END{
  if(rows<3){print "[CKM] need at least 3 numeric rows"; exit 3}
  # norms of columns ~1
  for(c=1;c<=3;c++){
    s=0; for(r=0;r<3;r++){s+=m[r,c]*m[r,c]}
    if(!near(s,1)){printf("[CKM] column %d norm^2=%g\n",c,s); rc=1}
  }
  # orthogonality of distinct columns ~0
  for(c1=1;c1<=3;c1++)for(c2=c1+1;c2<=3;c2++){
    dot=0; for(r=0;r<3;r++){dot+=m[r,c1]*m[r,c2]}
    if(!(abs(dot)<=tol)){printf("[CKM] cols %d,%d dot=%g\n",c1,c2,dot); rc=1}
  }
  if(rc==0) print "[CKM] ok unitary within tol=" tol;
  exit rc
}' "$f" || rc=$?
exit ${rc:-0}
