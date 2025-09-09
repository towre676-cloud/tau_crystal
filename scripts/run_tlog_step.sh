#!/usr/bin/env bash
set -euo pipefail
set +H
RECEIPT_PATH="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
scripts/ci_hardening/fingerprint_runner.sh .tau_ledger/runner_fingerprint.json
scripts/ci_hardening/receipt_patch_fingerprint.sh .tau_ledger/receipt.json .tau_ledger/runner_fingerprint.json
out="$(RECEIPT_PATH="$RECEIPT_PATH" scripts/tlog_append.sh)"
printf "%s\n" "$out" | sed "s/^/[tlog] /" >> "${GITHUB_STEP_SUMMARY:-/dev/null}" || true
while IFS="=" read -r k v; do
  case "$k" in tlog_leaf|tlog_root|tlog_index|tlog_algo) printf "%%s=%%s\n" "$k" "$v" >> "${GITHUB_OUTPUT:-/dev/null}";; esac
done <<< "$out"
