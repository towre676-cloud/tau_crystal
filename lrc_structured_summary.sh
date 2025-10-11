#!/usr/bin/env sh
# Usage: ./lrc_structured_summary.sh structured.csv > summary.csv
# Header expected:
# N,k,family,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,
# disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,
# s_den_divides_N,agree_max,why_miss,thr_num,thr_den,slack_num,slack_den,beats_bound
CSV="${1:-lrc_structured.csv}"

awk -F, '
NR==1 { next }
{
  k = $2 + 0
  sN = $20 + 0
  sD = $21 + 0
  total[k]++

  if (sN == 0) {
    exact[k]++
  } else if (sN > 0) {
    beat[k]++
    over_sum[k] += (sD ? sN/sD : 0)
    val = (sD ? sN/sD : 0)
    if (!(k in over_max) || val > over_max[k]) { over_max[k] = val }
  } else {
    miss[k]++
    gap = (sD ? (-sN)/sD : 0)
    under_sum[k] += gap
    if (!(k in under_max) || gap > under_max[k]) { under_max[k] = gap }
  }
}
END {
  print "k,total,exact_hits,meet_or_beat,misses,hit_rate,meet_rate,mean_over,max_over,mean_gap,max_gap"
  for (k in total) {
    t  = total[k]
    ex = (k in exact ? exact[k] : 0)
    bt = (k in beat  ? beat[k]  : 0)
    ms = (k in miss  ? miss[k]  : 0)
    hr = (t ? ex/t : 0)
    mr = (t ? (ex+bt)/t : 0)
    mo = (bt ? over_sum[k]/bt : 0)
    mxo= (k in over_max ? over_max[k] : 0)
    mg = (ms ? under_sum[k]/ms : 0)
    mxg= (k in under_max ? under_max[k] : 0)
    printf "%d,%d,%d,%d,%d,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f\n",
           k,t,ex,ex+bt,ms,hr,mr,mo,mxo,mg,mxg
  }
}
' "$CSV" | sort -t, -k1,1n
