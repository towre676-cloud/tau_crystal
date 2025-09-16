#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

HITS="analysis/discovery_hits.tsv"
BEST="analysis/discovery_best.tsv"
HEEG="analysis/analytic_heegner.tsv"

OUT_SUM="analysis/rollup_summary.tsv"
OUT_HNK="analysis/hist_discovery_Nk.tsv"
OUT_HL0="analysis/hist_rank_L0.tsv"

# ----- summary -----
{
  # discovery counts
  if [ -s "$HITS" ]; then
    hits=$(awk 'NR>1{c++} END{print c+0}' "$HITS")
    echo -e "discovery_hits\t$hits"
    mean_best=$(awk 'NR==1{print $1}' "$BEST" 2>/dev/null || echo "")
    [ -n "$mean_best" ] && echo -e "discovery_best_mean_r\t$mean_best" || true
  else
    echo -e "discovery_hits\t0"
  fi

  # rank-2 count + median L0
  if [ -s "$HEEG" ]; then
    awk -F'\t' '
      NR>1 { L0[++n]=$2+0; if($11+0>=2) r2++ }
      END{
        # median via gawk asort (expected on Git Bash)
        if(n>0){ asort(L0); mid=int((n+1)/2); 
          med=( (n%2)? L0[mid] : (L0[mid]+L0[mid+1])/2 ); 
          printf "rank2_candidates\t%d\nmedian_L0\t%.16g\n", r2+0, med+0
        } else {
          print "rank2_candidates\t0"; print "median_L0\tNaN"
        }
      }' "$HEEG"
  else
    echo -e "rank2_candidates\t0"
    echo -e "median_L0\tNaN"
  fi
} > "$OUT_SUM"

# ----- histogram over (N decade, k bin) from discovery_hits.tsv -----
# columns: mean_r  min_r  N  k  tested  primes ...
if [ -s "$HITS" ]; then
  awk -F'\t' -v kbw="${K_BIN_WIDTH:-4}" '
    NR==1{next}
    {
      N=$3+0; k=$4+0; mr=$1+0
      if(N<=0){next}
      dec=int(log(N)/log(10))           # N decade
      kbin=int(k/kbw)*kbw               # lower edge of k bin
      key=dec"\t"kbin
      cnt[key]++; sum[key]+=mr
    }
    END{
      print "N_decade\tk_bin\tcount\tmean_of_mean_r"
      for(k in cnt){
        printf "%s\t%d\t%.16g\n", k, cnt[k], sum[k]/cnt[k]
      }
    }' "$HITS" | sort -k1,1n -k2,2n > "$OUT_HNK"
else
  printf "N_decade\tk_bin\tcount\tmean_of_mean_r\n" > "$OUT_HNK"
fi

# ----- histogram of |L0| magnitude (log10 bins) & rank2 per bin -----
# heeg cols: phi L0 Lprime Omega Height deltas sign_changes slope_avg curve_avg rank_guess
if [ -s "$HEEG" ]; then
  awk -F'\t' '
    NR==1{next}
    {
      L0=$2+0; r=$11+0
      a=(L0<0?-L0:L0)
      if(a==0){b="10^-inf"} else { b= sprintf("10^{%d}", int(log(a)/log(10))) }
      cnt[b]++; if(r>=2) r2[b]++
    }
    END{
      print "L0_bin\tcount\trank2_in_bin"
      for(b in cnt){ printf "%s\t%d\t%d\n", b, cnt[b], r2[b]+0 }
    }' "$HEEG" | sort -t'^' -k2,2n > "$OUT_HL0"
else
  printf "L0_bin\tcount\trank2_in_bin\n" > "$OUT_HL0"
fi

echo "[rollups] wrote: $OUT_SUM, $OUT_HNK, $OUT_HL0"
