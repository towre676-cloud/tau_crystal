#!/usr/bin/env bash
set -euo pipefail
set +H
RECEIPT="${1:-.tau_ledger/receipt.json}"
FPR="${2:-.tau_ledger/runner_fingerprint.json}"
[[ -f "$RECEIPT" ]] || { echo "[err] missing $RECEIPT"; exit 3; }
[[ -f "$FPR" ]] || { echo "[err] missing $FPR"; exit 3; }
tmp="$(mktemp 2>/dev/null || printf ".rcpt.tmp.%s" "$$")"
jq --slurpfile fp "$FPR" '.runner=($fp[0])' "$RECEIPT" >"$tmp"
mv -f "$tmp" "$RECEIPT"
