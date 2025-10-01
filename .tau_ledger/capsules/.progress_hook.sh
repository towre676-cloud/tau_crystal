#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
# Only run if a table was produced
[ -f analysis/progress.tsv ] || exit 0
CAPS="fail"; scripts/capsules/verify.sh >/dev/null 2>&1 && CAPS="ok"
UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)
TMP=".tau_ledger/capsules/.progress.fixed"; mkdir -p "$(dirname "$TMP")"
{
  IFS= read -r header || true; printf "%s\n" "$header"
  # Print all rows except capsules_verify
  tail -n +2 analysis/progress.tsv | grep -v -E '^capsules_verify[[:space:]]' || true
  # Append authoritative row
  if [ "$CAPS" = "ok" ]; then
    printf "capsules_verify\tok\t%s\t-\n" "$UTC"
  else
    printf "capsules_verify\tfail\t-\t[CAPVERIFY] mismatch\n"
  fi
} > "$TMP"
mv "$TMP" analysis/progress.tsv
exit 0
