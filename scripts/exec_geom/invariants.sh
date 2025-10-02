#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
CONF=${1:-.exec_geom/symbol.conf}
EXC=${2:-.exec_geom/exceptionals.tsv}
out_dir=.tau_ledger/exec_geom
mkdir -p "$out_dir"
epsilon=o1; g=0; b=0; base_orientable=1; total_orientable=1
[ -f "$CONF" ] && while IFS='=' read -r k v; do
  case "$k" in
    epsilon) epsilon=$v;; g) g=$v;; b) b=$v;; base_orientable) base_orientable=$v;; total_orientable) total_orientable=$v;;
  esac
done < "$CONF"
tmp_exc=.exec_geom/.exc.310
awk 'BEGIN{FS="\t"} NR==1{next} NF>=2{if($1+0>0){print $1"\t"$2}}' "$EXC" > "$tmp_exc" || true
sum_b_over_a=0
sum_one_minus_inv=0
L=1
gcd(){ a=$1; b=$2; while [ "$b" -ne 0 ]; do t=$((a%%b)); a=$b; b=$t; done; echo "$a"; }
lcm2(){ x=$1; y=$2; [ "$x" -eq 0 ] && echo 0 && return; g=$(gcd "$x" "$y"); echo $(( x / g * y )); }
while IFS=$'\t' read -r a b_i; do
  if [ -n "$a" ] && [ -n "$b_i" ]; then
    sum_b_over_a=$(awk -v s="$sum_b_over_a" -v bi="$b_i" -v ai="$a" 'BEGIN{printf "%.12f", s + (bi+0.0)/(ai+0.0)}')
    sum_one_minus_inv=$(awk -v s="$sum_one_minus_inv" -v ai="$a" 'BEGIN{printf "%.12f", s + (1.0 - 1.0/(ai+0.0))}')
    L=$(lcm2 "$L" "$a")
  fi
done < "$tmp_exc"
if [ "$base_orientable" -eq 1 ]; then
  chiB0=$((2 - 2*g))
else
  chiB0=$((2 - g))
fi
chiB=$(awk -v c0="$chiB0" -v s="$sum_one_minus_inv" 'BEGIN{printf "%.12f", (c0+0.0) - s}')
einv=$(awk -v b0="$b" -v s="$sum_b_over_a" 'BEGIN{printf "%.12f", (b0+0.0) + s}')
geoclass=""
sign=$(awk -v x="$chiB" 'BEGIN{if(x>1e-12)print 1; else if (x<-1e-12) print -1; else print 0}')
if [ "$sign" -gt 0 ]; then geoclass="spherical_or_S2xR"; fi
if [ "$sign" -eq 0 ]; then geoclass="euclidean_or_nil"; fi
if [ "$sign" -lt 0 ]; then geoclass="SL2R_tilde_or_H2xR"; fi
cover_trivial="false"
if awk -v e="$einv" 'BEGIN{exit !(e>-1e-12 && e<1e-12)}'; then cover_trivial="true"; fi
ts=$(date -u +%Y%m%dT%H%M%SZ)
rep="$out_dir/report_$ts.json"
: > "$rep"
printf "%s\n" "{" >> "$rep"
printf "%s\n" "  \"epsilon\": \"$epsilon\"," >> "$rep"
printf "%s\n" "  \"g\": $g," >> "$rep"
printf "%s\n" "  \"b\": $b," >> "$rep"
printf "%s\n" "  \"base_orientable\": $base_orientable," >> "$rep"
printf "%s\n" "  \"total_orientable\": $total_orientable," >> "$rep"
printf "%s\n" "  \"sum_b_over_a\": $sum_b_over_a," >> "$rep"
printf "%s\n" "  \"sum_one_minus_inv\": $sum_one_minus_inv," >> "$rep"
printf "%s\n" "  \"chiB0\": $chiB0," >> "$rep"
printf "%s\n" "  \"chiB\": $chiB," >> "$rep"
printf "%s\n" "  \"e_invariant\": $einv," >> "$rep"
printf "%s\n" "  \"L_period\": $L," >> "$rep"
printf "%s\n" "  \"geometry_class\": \"$geoclass\"," >> "$rep"
printf "%s\n" "  \"cover_trivial\": $cover_trivial," >> "$rep"
printf "%s\n" "  \"timestamp\": \"$ts\"" >> "$rep"
printf "%s\n" "}" >> "$rep"
ln -sf "$(basename "$rep")" "$out_dir/latest.json"
sha256sum "$rep" | awk '{print $1}' > "$out_dir/latest.sha256"
echo "[exec-geom] chi(B)=$chiB e=$einv L=$L class=$geoclass cover_trivial=$cover_trivial"
