#!/usr/bin/env bash
# Build canonical leaf JSON, append to NDJSON, advance Merkle frontier,
# and patch receipt exactly once with tlog_* fields.
set -euo pipefail
set +H
umask 022

RECEIPT="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
TLOG=".tau_ledger/tlog.ndjson"

command -v jq >/dev/null 2>&1 || { echo "[err] jq required"; exit 2; }

TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
RUN_ID="${GITHUB_RUN_ID:-0}"
REPO_URL="${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-unknown}"
COMMIT="${GITHUB_SHA:-$(git rev-parse HEAD 2>/dev/null || echo unknown)}"

if [[ ! -f "$RECEIPT" ]]; then echo "[err] missing receipt: $RECEIPT"; exit 3; fi

leaf_json="$(jq -c --arg ts "$TS" --arg rid "$RUN_ID" --arg repo "$REPO_URL" --arg commit "$COMMIT" '{version:"tlog-1",timestamp:$ts,repo:$repo,commit:$commit,run_id:$rid, receipt_digest:(input | .receipt_digest // empty), receipt_algo:(input | .receipt_algo // empty), grammar_digest:.grammar_digest, grammar_algo:.grammar_algo, statement_digest:.statement_digest, statement_algo:.statement_algo}' "$RECEIPT" <<< "{}")"

mkdir -p "$(dirname "$TLOG")"
printf "%s\n" "$leaf_json" >> "$TLOG"

if [[ ! -x scripts/merkle_frontier.sh ]]; then
  if [[ -x scripts/merkle_log.sh ]]; then cp -f scripts/merkle_log.sh scripts/merkle_frontier.sh; chmod +x scripts/merkle_frontier.sh; else echo "[err] missing scripts/merkle_frontier.sh"; exit 4; fi
fi

out="$(printf "%s" "$leaf_json" | scripts/merkle_frontier.sh append)"

leaf_digest=""; tlog_root=""; tlog_index=""; tlog_algo=""
while IFS="=" read -r k v; do
  case "$k" in
    leaf_digest|tlog_root|tlog_index|tlog_algo) eval "$k=\\"$v\\"" ;;
  esac
done <<< "$out"

tmp="$(mktemp 2>/dev/null || printf ".tlog.tmp.%s" "$$")"
jq --arg leaf "$leaf_digest" --arg root "$tlog_root" --arg idx "$tlog_index" --arg alg "$tlog_algo" '.tlog_leaf=$leaf | .tlog_root=$root | .tlog_index=($idx|tonumber) | .tlog_algo=$alg' "$RECEIPT" > "$tmp"
mv -f "$tmp" "$RECEIPT"

echo "tlog_leaf=$leaf_digest"
echo "tlog_root=$tlog_root"
echo "tlog_index=$tlog_index"
echo "tlog_algo=$tlog_algo"
