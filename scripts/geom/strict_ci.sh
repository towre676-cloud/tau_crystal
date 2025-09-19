#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
DIR="${1:-.tau_ledger/geom}"
[ -d "$DIR" ] || { echo "[strict] no receipts dir: $DIR"; exit 2; }
scripts/geom/judge.sh "$DIR" >/dev/null || { echo "[strict] judge failed"; exit 3; }
TX="analysis/geom/transcript.tsv"
[ -s "$TX" ] || { echo "[strict] no transcript"; exit 4; }
bad=0
while IFS=$'\t' read -r rid kind file accept ts tag param hA hB rid_ok hA_ok hB_ok; do
  [ "$rid" = "rid" ] && continue
  if [ "$kind" = "infer" ] && [ "${accept:-0}" != "1" ]; then echo "[strict] infer not accepted: $file"; bad=1; fi
  if [ "${rid_ok:-}" = "0" ]; then echo "[strict] RID recompute failed: $file"; bad=1; fi
  if [ -n "$hA" ] && [ "${hA_ok:-1}" = "0" ]; then echo "[strict] hA mismatch: $file"; bad=1; fi
  if [ -n "$hB" ] && [ "${hB_ok:-1}" = "0" ]; then echo "[strict] hB mismatch: $file"; bad=1; fi
done < "$TX"
[ "$bad" -eq 0 ] && echo "[strict] PASS" || { echo "[strict] FAIL"; exit 5; }
