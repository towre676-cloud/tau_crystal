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
    [ -n "$mean_best" ] && echo -e "discovery_best_mean_r\t$mean_best"
  else
    echo -e "discovery_hits\t0"
  fi

  # rank counts + median L0 + adaptive taus + correlations + spectral stats
  if [ -s "$HEEG" ]; then
    awk -F'\t' '
      NR==1{next}
      { L0[++n]=$2+0; r=$15+0; if(r>=2) r2++ }  # note: rank_guess column index 15 (matches gate v4)
      END{
        # median & quantiles (GNU awk asort)
        if(n>0){
          asort(L0)
          mid=int((n+1)/2)
          med=( (n%2)? L0[mid] : (L0[mid]+L0[mid+1])/2 )
          q10=L0[int(n*0.10)]; q05=L0[int(n*0.05)]
          printf "rank2_candidates\t%d\nmedian_L0\t%.16g\nadaptive_tau_L0_10pct\t%.16g\nadaptive_tau_L0_5pct\t%.16g\n", r2+0, med+0, q10+0, q05+0
        } else {
          print "rank2_candidates\t0"; print "median_L0\tNaN"; print "adaptive_tau_L0_10pct\tNaN"; print "adaptive_tau_L0_5pct\tNaN"
        }
      }' "$HEEG"

    # correlation & spectral gaps from L0 stream
    awk -F'\t' '
      NR==1{next}
      { L[++n]=$2+0 }
      END{
        if(n>=3){
          # second-difference variance
          for(i=1;i<n;i++){ diff[i]=L[i+1]-L[i] }
          m=0; for(i=1;i<n;i++) m+=diff[i]; m/= (n-1)
          var=0; for(i=1;i<n;i++){ d=diff[i]-m; var+=d*d } ; var/= (n-1)

          # spectral gap ratios (nearest-neighbor)
          asort(L)
          gcount=0
          for(i=1;i<n;i++){ gap[i]=L[i+1]-L[i] }
          # clean positive gaps
          for(i=1;i<n;i++) if(gap[i]>0) { G[++gcount]=gap[i] }
          ratio_mean="NaN"
          if(gcount>=2){
            sumr=0; for(i=1;i<gcount;i++) sumr += G[i+1]/G[i]
            ratio_mean = sumr/(gcount-1)
          }
          printf "sec_diff_var\t%.16g\nspectral_ratio_mean\t%s\n", var, ratio_mean
        } else {
          print "sec_diff_var\tNaN"; print "spectral_ratio_mean\tNaN"
        }
      }' "$HEEG"
  else
    echo -e "rank2_candidates\t0\nmedian_L0\tNaN\nadaptive_tau_L0_10pct\tNaN\nadaptive_tau_L0_5pct\tNaN\nsec_diff_var\tNaN\nspectral_ratio_mean\tNaN"
  fi
} > "$OUT_SUM"

# ----- (N,k) histogram from discovery_hits.tsv -----
if [ -s "$HITS" ]; then
  awk -F'\t' -v kbw="${K_BIN_WIDTH:-4}" '
    NR==1{next}
    { N=$3+0; k=$4+0; mr=$1+0; if(N<=0)next;
      dec=int(log(N)/log(10)); kbin=int(k/kbw)*kbw; key=dec"\t"kbin; cnt[key]++; sum[key]+=mr
    }
    END{
      print "N_decade\tk_bin\tcount\tmean_of_mean_r"
      for(k in cnt){ printf "%s\t%d\t%.16g\n", k, cnt[k], sum[k]/cnt[k] }
    }' "$HITS" | sort -k1,1n -k2,2n > "$OUT_HNK"
else
  printf "N_decade\tk_bin\tcount\tmean_of_mean_r\n" > "$OUT_HNK"
fi

# ----- |L0| histogram with rank2 counts -----
if [ -s "$HEEG" ]; then
  awk -F'\t' '
    NR==1{next}
    { L0=$2+0; r=$15+0; a=(L0<0?-L0:L0); bin=(a==0?"10^-inf":sprintf("10^{%d}", int(log(a)/log(10)))); cnt[bin]++; if(r>=2) r2[bin]++ }
    END{
      print "L0_bin\tcount\trank2_in_bin"
      for(b in cnt){ printf "%s\t%d\t%d\n", b, cnt[b], r2[b]+0 }
    }' "$HEEG" | sort -t'^' -k2,2n > "$OUT_HL0"
else
  printf "L0_bin\tcount\trank2_in_bin\n" > "$OUT_HL0"
fi

echo "[rollups] wrote: $OUT_SUM, $OUT_HNK, $OUT_HL0"
