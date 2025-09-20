#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_t1="$1"; A_t2="$2"; B="$3"; eps="${4:-0.01}"; delta="${5:-0.02}"; tau="${6:-0.03}"
[ -f "$A_t1" ] && [ -f "$A_t2" ] && [ -f "$B" ] || { echo "VERIFY=FALSE  RID="; exit 0; }
read a_ok a_rid <<<"$(scripts/geom/anchor_rule.sh "$A_t1" "$A_t2" "$eps" "$delta")"
if [ "$a_ok" != "TRUE" ]; then
  printf "%s\n" "ANCHOR=FALSE RID_ANCHOR=$a_rid" > "receipts/geom/${a_rid%% *}.receipt"
  echo "VERIFY=FALSE  RID=$a_rid"; exit 0
fi
read v_ok v_rid <<<"$(scripts/geom/verify_rule.sh "$A_t1" "$B" "$tau")"
printf "%s\n" "ANCHOR=TRUE RID_ANCHOR=$a_rid" > "receipts/geom/${a_rid%% *}.receipt"
printf "%s\n" "VERIFY=$v_ok RID_VERIFY=$v_rid" > "receipts/geom/${v_rid%% *}.receipt"
echo "VERIFY=$v_ok  RID=$v_rid"
