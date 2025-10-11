#!/usr/bin/env sh
in="${1:-lrc_structured.csv}"
awk -F, 'BEGIN{OFS=","}
NR==1{print; next}
{
  if ($15=="NO" && ($17=="" || $17==" ")) {
    csn=$5+0; csd=$6+0;
    a=(csn<0?-csn:csn); b=(csd<0?-csd:csd);
    while(b){t=a%b; a=b; b=t}
    g=(a?a:1);
    $17 = (csn/g) "/" (csd/g)
  }
  print
}' "$in"
