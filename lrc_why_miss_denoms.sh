#!/usr/bin/env sh
# Usage: ./lrc_why_miss_denoms.sh structured.csv > denoms_by_k.txt
CSV="${1:-lrc_structured.csv}"
# Normalize CRLF on input, extract denominators for rows where s_den_divides_N=NO
tr -d '\r' < "$CSV" | awk -F, 'NR==1{next}
{
  # 1:N 2:k 6:cont_s_den 15:s_den_divides_N 17:why_miss
  if($15=="NO"){
     d = $17
     if (d ~ /\/[0-9]+$/) { split(d,xy,"/"); D = xy[2]+0 }
     else { D = $6+0 }  # fallback: continuous s_den
     if (D>0) print $2","D
  }
}' | sort -u
