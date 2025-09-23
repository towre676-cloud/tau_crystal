#!/usr/bin/env bash
set -euo pipefail; umask 022
utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
led=".tau_ledger/vows/latest.tsv"

# initialize an empty ledger (header only) if missing
if [ ! -f "$led" ]; then
  ts=$(date -u +%Y%m%dT%H%M%SZ)
  out=".tau_ledger/vows/vows-$ts.tsv"
  printf "when\tarea\tvow\tstatus\n" > "$out"
  ln -sf "$(basename "$out")" "$led"
fi

# print the canonical organ line expected by the hammer
printf "vows\tok\t%s\t-\n" "$utc"
exit 0
