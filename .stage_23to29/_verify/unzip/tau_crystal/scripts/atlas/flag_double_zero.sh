#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

# Product of local factors via log sum:
# L(s) ≈ ∏_p (1 - a_p p^{-s} + p^{1-2s})^{-1}
L_at_s() { awk -v s="$1" '
  BEGIN{FS="\t"; sum=0; used=0}
  NR==1{next}
  {
    p=$1+0; ap=$2+0
    # den = 1 - ap/p^s + p^{1-2s}
    ps = exp(s*log(p))
    p1m2s = exp((1.0 - 2.0*s)*log(p))
    den = 1.0 - ap/ps + p1m2s
    if (den<=0) den=1e300
    sum += -log(den); used++
  }
  END{printf "%.16f", exp(sum)}
' "$2"; }

out="analysis/atlas/candidates.tsv"
printf "label\tN\tw\tpcount\tLhalf\tslope\tbound\tpanel\n" > "$out"
delta="0.02"

for leaf in analysis/atlas/*/leaf.json; do
  [ -s "$leaf" ] || continue
  label=$(jq -r '.curve.label' "$leaf")
  N=$(jq -r '.curve.conductor' "$leaf")
  panel=$(jq -r '.panel.path' "$leaf")
  pcount=$(jq -r '.panel.primes_evaluated' "$leaf")
  [ "$pcount" -ge 20 ] || continue

  w=$(jq -r '.checks.parity.root_number // "unknown"' "$leaf")
  bound=$(jq -r '.numerics.tail_proxy.half // "0.001"' "$leaf")

  L0=$(L_at_s 0.5 "$panel")
  Lp=$(awk -v d="$delta" 'BEGIN{printf "%.5f", 0.5+d}')
  Lp=$(L_at_s "$Lp" "$panel")
  Lm=$(awk -v d="$delta" 'BEGIN{printf "%.5f", 0.5-d}')
  Lm=$(L_at_s "$Lm" "$panel")
  slope=$(awk -v lp="$Lp" -v lm="$Lm" -v d="$delta" 'BEGIN{printf "%.16f", (lp-lm)/(2*d)}')

  even_ok=$([ "$w" = "1" ] || [ "$w" = "+1" ] || [ "$w" = "unknown" ] && echo 1 || echo 0)
  tiny_L=$(awk -v x="$L0" -v b="$bound" 'BEGIN{if(x<0)x=-x; print (x<b)?1:0}')
  tiny_S=$(awk -v s="$slope" -v b="$bound" -v d="$delta" 'BEGIN{if(s<0)s=-s; print (s < (b/d))?1:0}')

  if [ "$even_ok" -eq 1 ] && [ "$tiny_L" -eq 1 ] && [ "$tiny_S" -eq 1 ]; then
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$label" "$N" "$w" "$pcount" "$L0" "$slope" "$bound" "$panel" >> "$out"
  fi
done

echo "[atlas] double-zero prefilter wrote: $out"
