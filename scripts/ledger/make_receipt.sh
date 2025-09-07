#!/usr/bin/env bash
set -euo pipefail
LEDGER_DIR=".tau_ledger"
CHAIN_FILE="${LEDGER_DIR}/CHAIN"
RECEIPTS_DIR="${LEDGER_DIR}/receipts"
mkdir -p "$RECEIPTS_DIR"

ts="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
head_sha="$(git rev-parse --verify --short HEAD 2>/dev/null || echo 'detached')"
run_id="${GITHUB_RUN_ID:-local}"
plan="${TAU_PLAN:-FREE}"
proofs="${TAU_REQUIRE_PROOFS:-false}"
laurent="${TAU_LAURENT_ENABLED:-false}"
ret="${TAU_RETENTION_DAYS:-14}"
maxw="${TAU_MAX_WORKERS:-2}"
merkle="$(grep -E '^MERKLE_ROOT:' docs/manifest.md 2>/dev/null | awk '{print $2}')"
[ -n "$merkle" ] || merkle="unknown"

prev="GENESIS"
[ -f "$CHAIN_FILE" ] && prev="$(tail -n1 "$CHAIN_FILE" | awk '{print $1}')" || true

rid="$(date -u +%Y%m%dT%H%M%SZ)-${head_sha}-${run_id}"
rcpt="${RECEIPTS_DIR}/${rid}.json"

# write tiny JSON (no jq)
{
  echo "{"
  echo "  \"id\": \"${rid}\","
  echo "  \"ts\": \"${ts}\","
  echo "  \"git\": \"${head_sha}\","
  echo "  \"plan\": \"${plan}\","
  echo "  \"proofs\": \"${proofs}\","
  echo "  \"laurent\": \"${laurent}\","
  echo "  \"retention_days\": \"${ret}\","
  echo "  \"max_workers\": \"${maxw}\","
  echo "  \"merkle_root\": \"${merkle}\","
  echo "  \"prev\": \"${prev}\""
  echo "}"
} > "$rcpt"

hash="$(sha256sum "$rcpt" | awk '{print $1}')"
echo "${hash} ${rcpt}" >> "$CHAIN_FILE"

printf '[ledger] receipt=%s hash=%s prev=%s\n' "$rcpt" "$hash" "$prev" >&2
echo "TAU_RECEIPT_ID=${rid}"
echo "TAU_RECEIPT_HASH=${hash}"
