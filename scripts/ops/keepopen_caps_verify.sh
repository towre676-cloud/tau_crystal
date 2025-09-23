#!/usr/bin/env bash
set +e
set +H; umask 022; export LC_ALL=C LANG=C
TMP=".tau_ledger/capsules"; mkdir -p "$TMP" analysis

CAPOK=1
if scripts/capsules/verify.sh; then STATUS="ok"; ERR="-"; else STATUS="fail"; ERR="[CAPVERIFY] mismatch"; CAPOK=0; fi
UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)

bash scripts/meta/progress_print.sh > "$TMP/progress.new.tsv" 2>"$TMP/progress.err" || true
{
  # Print header untouched
  IFS= read -r header < "$TMP/progress.new.tsv" || true
  printf "%s\n" "$header"
  # Stream remaining rows, drop any existing capsules_verify, print the rest verbatim
  tail -n +2 "$TMP/progress.new.tsv" | while IFS= read -r line; do
    first=$(printf "%s" "$line" | cut -f1)
    if [ "$first" = "capsules_verify" ]; then continue; fi
    printf "%s\n" "$line"
  done
  # Append authoritative capsules_verify row
  if [ "$STATUS" = "ok" ]; then
    printf "capsules_verify\tok\t%s\t-\n" "$UTC"
  else
    printf "capsules_verify\tfail\t-\t[CAPVERIFY] mismatch\n"
  fi
} > "$TMP/progress.fixed.tsv"
cp -f "$TMP/progress.fixed.tsv" analysis/progress.tsv

printf "=== progress.tsv (top) ===\n"; sed -n "1,50p" analysis/progress.tsv

show_tail () {
  title="$1"; shift; printf "\n=== %s ===\n" "$title";
  for f in "$@"; do [ -e "$f" ] || continue; printf "\n--- %s ---\n" "$f"; tail -n 30 "$f"; done
}
latest_gates=$(ls -1t .tau_ledger/gates/report.*.txt 2>/dev/null | head -n 2)
latest_hammer=$(ls -1t .tau_ledger/logs/hammer_*.log 2>/dev/null | head -n 1)
latest_cap=$(ls -1t .tau_ledger/logs/capverify_*.log 2>/dev/null | head -n 1)
show_tail "gate reports" $latest_gates
show_tail "hammer logs" $latest_hammer
show_tail "capverify logs" $latest_cap

if [ "${1:-}" = "--ci-status" ]; then if [ "$CAPOK" -eq 1 ]; then exit 0; else exit 1; fi; fi
if [ "$CAPOK" -eq 0 ]; then echo "[KEEPOPEN] verifier is RED (mismatch)"; else echo "[KEEPOPEN] verifier is GREEN"; fi
exit 0
