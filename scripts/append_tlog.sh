#!/usr/bin/env bash
set -euo pipefail
RECEIPT_PATH="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
STATEMENT_FILE="${STATEMENT_FILE:-lake-manifest.json}"
mkdir -p .tau_ledger
# b3sum shim
if ! command -v b3sum >/dev/null 2>&1; then b3sum(){ sha256sum "$@"; }; export -f b3sum 2>/dev/null || true; fi
[ -s "$RECEIPT_PATH" ] || { echo "[err] receipt missing: $RECEIPT_PATH"; exit 2; }
if [ ! -s "$STATEMENT_FILE" ]; then
  printf '{ "note": "synthetic statement" }\n' > .tau_ledger/statement.json
  STATEMENT_FILE=".tau_ledger/statement.json"
fi
R_HASH="$(b3sum "$RECEIPT_PATH" | awk '{print $1}')"
S_HASH="$(b3sum "$STATEMENT_FILE" | awk '{print $1}')"
RUN_ID="${GITHUB_RUN_ID:-0}"
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
REPO="${GITHUB_REPOSITORY:-unknown}"
COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
LINE="{\"version\":\"tlog-1\",\"timestamp\":\"$TS\",\"repo\":\"$REPO\",\"commit\":\"$COMMIT\",\"run_id\":\"$RUN_ID\",\"receipt_blake3\":\"$R_HASH\",\"statement_blake3\":\"$S_HASH\"}"
# local default: no signing; set SIGN=1 in CI if you add a key
if [ "${SIGN:-0}" = "1" ] && [ -n "${ED25519_SK_PEM:-}" ]; then
  TMP="$(mktemp)"; printf '%s' "$LINE" > "$TMP"
  SK="$(mktemp)"; printf '%s\n' "$ED25519_SK_PEM" > "$SK"; chmod 600 "$SK"
  SIG_BIN="$(mktemp)"
  if openssl pkeyutl -sign -inkey "$SK" -in "$TMP" -out "$SIG_BIN" >/dev/null 2>&1; then
    SIG_B64="$(base64 -w0 "$SIG_BIN" 2>/dev/null || base64 "$SIG_BIN" | tr -d '\n')"
    LINE="${LINE%}"; LINE="${LINE%,}"; LINE="${LINE%}}" 
    LINE="${LINE},\"sig_ed25519_b64\":\"$SIG_B64\"}"
  else
    echo "[warn] openssl signing not available; writing unsigned entry"
  fi
  rm -f "$TMP" "$SK" "$SIG_BIN"
fi
echo "$LINE" >> .tau_ledger/tlog.ndjson
echo "[ok] appended .tau_ledger/tlog.ndjson"
