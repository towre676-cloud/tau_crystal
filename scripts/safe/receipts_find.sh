#!/usr/bin/env bash
set +H
set -euo pipefail
IFS=$(printf "\n\t")
REG=".tau_ledger/REGISTRY_ALL.tsv"
[ -f "$REG" ] || { printf "No %s. Run scripts/safe/receipts_refresh.sh first.\n" "$REG" >&2; exit 1; }
q="${1:-}"
if [ -z "$q" ]; then cat "$REG"; else printf "ts\ttype\tsha256\tmerkle_root\tsize_bytes\tsource\tpath\tgit_commit\tgit_status\n"; grep -i -- "$q" "$REG" || true; fi
