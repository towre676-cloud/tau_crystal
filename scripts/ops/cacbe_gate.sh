#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
scripts/ops/cacbe_lint.sh .
cp .tau_ledger/cacbe/scan_* .tau_ledger/cacbe/latest.tsv 2>/dev/null || true
scripts/ops/cacbe_attention.sh .tau_ledger/cacbe/latest.tsv
awk -F'\t' 'BEGIN{rc=0} NR>1{if($2==3 && $3>0) rc=66; if($4>=3) rc=66} END{exit rc}' .cacbe/attention.tsv
echo "[CACBE] gate ok; attention ledger updated"
