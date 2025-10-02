#!/usr/bin/env bash
set -euo pipefail; set +H
COVER="${1:-analysis/obstructions/cover1}"
OUT="analysis/obstructions/tpc_report.tsv"
mkdir -p "$(dirname "$OUT")"
norm(){ awk -F"\t" 'NF{print $1 "\t" $2}' "$1" 2>/dev/null | LC_ALL=C sort; }
hashf(){ (norm "$1" | sha256sum | awk "{print \$1}") 2>/dev/null || printf "NA"; }
join3eq(){ diff -u <(norm "$1") <(norm "$2") >/dev/null 2>&1 && diff -u <(norm "$2") <(norm "$3") >/dev/null 2>&1 && echo ok || echo FAIL; }
cover_id=$(awk -F"\t" '$1=="cover_id"{print $2}' "$COVER/meta.tsv" 2>/dev/null || echo "cover?")
kname=$(awk -F"\t" '$1=="kernel"{print $2}' "$COVER/meta.tsv" 2>/dev/null || echo "unknown")
m01a="$COVER/U0_to_01.tsv"; m01b="$COVER/U1_to_01.tsv"
m02a="$COVER/U0_to_02.tsv"; m02b="$COVER/U2_to_02.tsv"
m12a="$COVER/U1_to_12.tsv"; m12b="$COVER/U2_to_12.tsv"
t01="$COVER/U01_to_012.tsv"; t02="$COVER/U02_to_012.tsv"; t12="$COVER/U12_to_012.tsv"
pair01=$(join3eq "$m01a" "$m01b" "$m01b" | sed "s/ok/ok (sym)/")
pair02=$(join3eq "$m02a" "$m02b" "$m02b" | sed "s/ok/ok (sym)/")
pair12=$(join3eq "$m12a" "$m12b" "$m12b" | sed "s/ok/ok (sym)/")
triple=$(join3eq "$t01" "$t02" "$t12")
h01=$(hashf "$t01"); h02=$(hashf "$t02"); h12=$(hashf "$t12")
class=$([ "$triple" = "ok" ] && echo "H1=0" || echo "H1!=0")
if [ ! -s "$OUT" ]; then printf "cover_id\tkernel\tpair01\tpair02\tpair12\ttriple_ok\tclass\thash_U01\t\thash_U02\t\thash_U12\n" > "$OUT"; fi
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$cover_id" "$kname" "$pair01" "$pair02" "$pair12" "$triple" "$class" "$h01" "$h02" "$h12" >> "$OUT"
