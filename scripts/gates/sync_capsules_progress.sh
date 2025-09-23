#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
export LC_ALL=C LANG=C
TMP=".tau_ledger/capsules"; mkdir -p "$TMP"
CAPOK=1
if scripts/capsules/verify.sh; then STATUS=ok; ERR="-"; else STATUS=fail; ERR="[CAPVERIFY] mismatch"; CAPOK=0; fi
UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)
bash scripts/meta/progress_print.sh > "$TMP/progress.new.tsv" || true
{
  IFS= read -r header || true; printf "%s\n" "$header"
  while IFS= read -r line; do
    key=${line%%	*}
    if [ "$key" = "capsules_verify" ]; then
      if [ "$STATUS" = "ok" ]; then printf "capsules_verify\tok\t%s\t-\n" "$UTC"; else printf "capsules_verify\tfail\t-\t[CAPVERIFY] mismatch\n"; fi
    else
      printf "%s\n" "$line"
    fi
  done
} < "$TMP/progress.new.tsv" > "$TMP/progress.fixed.tsv"
mv "$TMP/progress.fixed.tsv" analysis/progress.tsv
sed -n "1,50p" analysis/progress.tsv
[ "$CAPOK" -eq 1 ]
