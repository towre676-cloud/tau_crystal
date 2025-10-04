#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
out="${1:-tests/known_truth/motives/period_demo.tsv}"
: > "$out"; printf "component\tvalue\n" >> "$out"
k1=2.718281828; k2=1.414213562; k3=3.141592654
c1=$(awk -v x="$k1" "BEGIN{printf \"%.12f\", log(x)}")
c2=$(awk -v x="$k2" "BEGIN{printf \"%.12f\", log(x)}")
c3=$(awk -v x="$k3" "BEGIN{printf \"%.12f\", log(x)}")
min=$(awk -v a="$c1" -v b="$c2" -v c="$c3" "BEGIN{m=a; if(b<m)m=b; if(c<m)m=c; printf \"%.12f\", m}")
s1=$(awk -v x="$c1" -v m="$min" "BEGIN{printf \"%.12f\", x-m}")
s2=$(awk -v x="$c2" -v m="$min" "BEGIN{printf \"%.12f\", x-m}")
s3=$(awk -v x="$c3" -v m="$min" "BEGIN{printf \"%.12f\", x-m}")
tot=$(awk -v a="$s1" -v b="$s2" -v c="$s3" "BEGIN{printf \"%.12f\", a+b+c}")
p1=$(awk -v x="$s1" -v t="$tot" "BEGIN{printf \"%.12f\", x/t}")
p2=$(awk -v x="$s2" -v t="$tot" "BEGIN{printf \"%.12f\", x/t}")
p3=$(awk -v x="$s3" -v t="$tot" "BEGIN{printf \"%.12f\", x/t}")
printf "alpha\t%s\n" "$p1" >> "$out"
printf "beta\t%s\n"  "$p2" >> "$out"
printf "gamma\t%s\n" "$p3" >> "$out"
echo "[ResidueComplex] wrote components to $out (sum ≈ 1.0)"
