#!/usr/bin/env sh
# Usage: ./lrc_summary.sh annotated.csv
CSV="${1:-lrc_random_results_annotated.csv}"
awk -F, 'NR==1{next}
{
  k=$2; hits=$13; ok=$8
  total[k]++
  if(hits=="YES") onbound[k]++
  if(ok=="YES")   okc[k]++
}
END{
  printf "k,total,OK,hit_bound,hit_rate\n"
  for(k in total){
    rate = (total[k]>0)? onbound[k]/total[k] : 0
    printf "%s,%d,%d,%d,%.3f\n",k,total[k],okc[k]+0,onbound[k]+0,rate
  }
}' "$CSV" | sort -n
