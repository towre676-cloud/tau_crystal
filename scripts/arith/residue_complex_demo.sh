#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
out="${1:-tests/known_truth/motives/period_demo.tsv}"
ledger="${LEDGER_DIR:-.tau_ledger}"
mkdir -p "$(dirname "$out")" "$ledger"
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
ts=$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || env TZ=UTC date +%Y%m%dT%H%M%SZ || date +%Y%m%dT%H%M%SZ)
curv="${ledger}/${ts}_curvature.tsv"
mean=$(awk -v a="$c1" -v b="$c2" -v c="$c3" "BEGIN{printf \"%.12f\", (a+b+c)/3}")
d1=$(awk -v x="$c1" -v m="$mean" "BEGIN{printf \"%.12f\", x-m}")
d2=$(awk -v x="$c2" -v m="$mean" "BEGIN{printf \"%.12f\", x-m}")
d3=$(awk -v x="$c3" -v m="$mean" "BEGIN{printf \"%.12f\", x-m}")
: > "$curv"
printf "alpha\t%s\n" "$d1" >> "$curv"
printf "beta\t%s\n"  "$d2" >> "$curv"
printf "gamma\t%s\n" "$d3" >> "$curv"
echo "[ResidueComplex] period→$out ; curvature→$curv (sum≈0)"
