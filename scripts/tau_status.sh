#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/_tau_common.sh"
ensure jq
LAST="$(ls -1 .tau_ledger/receipts/*.json 2>/dev/null | tail -n1 || true)"
[ -n "${LAST:-}" ] || { echo "no receipts yet"; exit 0; }
jq '{id, ts, trace}' "$LAST"
