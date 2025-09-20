#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_t1="$1"; A_t2="$2"; B="$3"; eps="${4:-0.01}"; delta="${5:-0.02}"; tau="${6:-0.03}"
[ -f "$A_t1" ] && [ -f "$A_t2" ] && [ -f "$B" ] || { echo "usage: A_t1.tsv A_t2.tsv B.tsv [eps] [delta] [tau]" >&2; exit 1; }
read a_ok a_rid <<<"$(scripts/geom/anchor_rule.sh "$A_t1" "$A_t2" "$eps" "$delta")"
if [ "$a_ok" != "TRUE" ]; then echo "ANCHOR=FALSE  RID=$a_rid"; exit 2; fi
read v_ok v_rid <<<"$(scripts/geom/verify_rule.sh "$A_t1" "$B" "$tau")"
printf "%s\n" "ANCHOR=TRUE RID_ANCHOR=$a_rid" > "receipts/geom/$(echo "$a_rid" | awk "{print \$1}").receipt"
printf "%s\n" "VERIFY=$v_ok RID_VERIFY=$v_rid" > "receipts/geom/$(echo "$v_rid" | awk "{print \$1}").receipt"
echo "VERIFY=$v_ok  RID=$v_rid"
