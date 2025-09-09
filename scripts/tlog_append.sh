#!/usr/bin/env bash
set -euo pipefail
RECEIPT_PATH="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
STATEMENT_FILE="${STATEMENT_FILE:-lake-manifest.json}"
test -s "$RECEIPT_PATH"  || { echo "[err] receipt missing: $RECEIPT_PATH" >&2; exit 2; }
test -s "$STATEMENT_FILE"|| { echo "[err] statement missing: $STATEMENT_FILE" >&2; exit 2; }
mkdir -p .tau_ledger
read -r R_DIG R_ALGO < <("$(dirname "$0")/hash.sh" "$RECEIPT_PATH")
read -r S_DIG S_ALGO < <("$(dirname "$0")/hash.sh" "$STATEMENT_FILE")
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"; RUN_ID="${GITHUB_RUN_ID:-0}"
REPO="${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-unknown}"
COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"

# entry (unsigned by default)
ENTRY_JSON="$(mktemp)"; {
  printf '{'
  printf '"version":"tlog-1",'
  printf '"timestamp":"%s",' "$TS"
  printf '"repo":"%s",' "$REPO"
  printf '"commit":"%s",' "$COMMIT"
  printf '"run_id":"%s",' "$RUN_ID"
  printf '"receipt_%s":"%s",'  "$R_ALGO" "$R_DIG"
  printf '"statement_%s":"%s"' "$S_ALGO" "$S_DIG"
  printf '}\n'
} > "$ENTRY_JSON"

# optional Ed25519 sign if key is provided
SIG_B64=""; PUB_PEM=""
if [ -n "${ED25519_SK_B64:-}" ]; then
  SK="$(mktemp)"; echo "$ED25519_SK_B64" | base64 -d > "$SK"; chmod 600 "$SK"
  SIG_BIN="$(mktemp)"
  if openssl pkeyutl -sign -inkey "$SK" -in "$ENTRY_JSON" -out "$SIG_BIN" 2>/dev/null; then
    SIG_B64="$(base64 -w0 "$SIG_BIN" 2>/dev/null || base64 "$SIG_BIN" | tr -d '\n')"
    PUB_PEM="$(openssl pkey -in "$SK" -pubout 2>/dev/null || true)"
  fi
  rm -f "$SIG_BIN" "$SK"
fi

# finalize line with optional signature
LINE="$(cat "$ENTRY_JSON")"
if [ -n "$SIG_B64" ]; then
  LINE="$(printf '%s' "$LINE" | sed 's/}$/,"sig_ed25519_b64":"'"$SIG_B64"'","pubkey_pem":'"$(printf '%s' "$PUB_PEM" | python3 -c 'import json,sys;print(json.dumps(sys.stdin.read()))')"'} /')"
fi

# append locally
echo "$LINE" >> .tau_ledger/tlog.ndjson

# simple Merkle: root = blake3(line) for now (single-leaf); upgrade later when shard is live
read -r LEAF_DIG LEAF_ALGO < <("$(dirname "$0")/hash.sh" <(printf '%s' "$LINE") )
ROOT_DIG="$LEAF_DIG"; ROOT_ALGO="$LEAF_ALGO"

# optional gist append if gh + TLOG_GIST_ID present
if [ -n "${TLOG_GIST_ID:-}" ] && command -v gh >/dev/null 2>&1; then
  TMPD="$(mktemp -d)"; (gh gist view "$TLOG_GIST_ID" --files --raw > "$TMPD/tlog.ndjson" || true)
  echo "$LINE" >> "$TMPD/tlog.ndjson"
  gh gist edit "$TLOG_GIST_ID" -a "$TMPD/tlog.ndjson#tlog.ndjson" >/dev/null 2>&1 || true
fi

# outputs
printf "tlog_leaf=%s\n"      "$LEAF_DIG"
printf "tlog_leaf_algo=%s\n" "$LEAF_ALGO"
printf "tlog_root=%s\n"      "$ROOT_DIG"
printf "tlog_root_algo=%s\n" "$ROOT_ALGO"
