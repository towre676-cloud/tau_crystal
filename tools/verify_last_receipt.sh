#!/usr/bin/env bash
set -euo pipefail
branch="$(git rev-parse --abbrev-ref HEAD)"
id="$(gh run list --workflow smart-ci --branch "$branch" --limit 1 --json databaseId -q ".[0].databaseId")"
[ -n "$id" ] || { echo "[err] no workflow runs found for branch $branch"; exit 1; }
rm -f .tau_ledger/receipt.json 2>/dev/null || true
gh run download "$id" --name smartcache-receipt -D .tau_ledger >/dev/null
python3 scripts/manifest_verify.py
