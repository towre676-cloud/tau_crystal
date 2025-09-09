#!/usr/bin/env bash
set -euo pipefail
mkdir -p .tau_ledger
KEY="${1:-unknown}"
STATUS="${2:-unknown}"
RUN_ID="${GITHUB_RUN_ID:-0}"
RUN_URL="https://github.com/${GITHUB_REPOSITORY:-unknown}/actions/runs/${RUN_ID}"
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
cat > .tau_ledger/receipt.json <<JSON
{
  "version": "rcpt-1",
  "timestamp": "$TS",
  "run_id": "$RUN_ID",
  "run_url": "$RUN_URL",
  "cache_key": "$KEY",
  "status": "$STATUS"
}
JSON
echo "[receipt] .tau_ledger/receipt.json"
