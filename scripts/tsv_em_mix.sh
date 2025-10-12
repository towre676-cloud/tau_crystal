#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_em_mix.sh <in.tsv> <A> <B> <out.tsv>}"; A="${2:?}"; B="${3:?}"; OUT="${4:?}"
sed -i 's/\r$//' "$IN" 2>/dev/null || true
awk -v OFS='\t' -v A="$A" -v B="$B" '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
function idx(name,i){name=canon(name); for(i=1;i<=NF;i++) if(canon($i)==name) return i; return -1}
NR==1{
  iu=idx("u"); ia=idx("a"); ia1=idx("a1"); ia2=idx("a2");
  iD=idx("aD"); iD1=idx("aD1"); iD2=idx("aD2");
  ip2=idx("p2"); ip1=idx("p1"); ip0=idx("p0"); iseed=idx("seed");
  if(iu<0||ia<0||ia1<0||ia2<0||iD<0||iD1<0||iD2<0||ip2<0||ip1<0||ip0<0){
    print "ERROR: expected u a a1 a2 aD aD1 aD2 p2 p1 p0 [seed]" > "/dev/stderr"; exit 2
  }
  printf "u\ta\ta1\ta2\tp2\tp1\tp0"; if(iseed>0) printf "\tseed"; printf "\n"; next
}
{
  u=$iu+0; a=$ia+0; a1=$ia1+0; a2=$ia2+0; aD=$iD+0; aD1=$iD1+0; aD2=$iD2+0;
  p2=$ip2+0; p1=$ip1+0; p0=$ip0+0; seed=(iseed>0?$iseed:"");
  an  = A*aD  + B*a;
  an1 = A*aD1 + B*a1;
  an2 = A*aD2 + B*a2;
  printf "%.15g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g", u, an, an1, an2, p2, p1, p0;
  if(iseed>0) printf "\t%s", seed; printf "\n";
}
' "$IN" > "$OUT"
