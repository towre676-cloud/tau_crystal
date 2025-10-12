#!/usr/bin/env bash
set +H
set -euo pipefail
IFS=$(printf "\n\t")
ROOT="$PWD"
printf "==> Scanning git history…\n"
[ -x scripts/safe/receipt_history.sh ] && scripts/safe/receipt_history.sh || printf " (skipped: scripts/safe/receipt_history.sh not present)\n"
printf "==> Scanning filesystem…\n"
[ -x scripts/safe/receipt_index.sh ] && scripts/safe/receipt_index.sh || printf " (skipped: scripts/safe/receipt_index.sh not present)\n"
printf "==> Merging shards…\n"
[ -x scripts/safe/registry_merge.sh ] && scripts/safe/registry_merge.sh || { printf "Missing scripts/safe/registry_merge.sh\n" >&2; exit 1; }
printf "==> Done. See .tau_ledger/REGISTRY_ALL.tsv\n"
