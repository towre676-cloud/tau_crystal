#!/usr/bin/env bash
set -euo pipefail

RECEIPT_PATH="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
STATEMENT_FILE="${STATEMENT_FILE:-lake-manifest.json}"
: "${TZ:=UTC}"
mkdir -p .tau_ledger

# dev shim: if b3sum missing (Windows), fall back to sha256sum so this still runs locally
if ! command -v b3sum >/dev/null 2>&1; then
  b3sum(){ sha256sum "$@"; }
  export -f b3sum 2>/dev/null || true
  echo "[warn] b3sum not found; using sha256sum shim (dev only)"
fi

if [ ! -s "$RECEIPT_PATH" ]; then echo "[err] receipt missing: $RECEIPT_PATH"; exit 2; fi
if [ ! -s "$STATEMENT_FILE" ]; then echo "[skip] statement missing: $STATEMENT_FILE"; exit 0; fi

R_HASH="$(b3sum "$RECEIPT_PATH"   | awk '{print $1}')"
S_HASH="$(b3sum "$STATEMENT_FILE" | awk '{print $1}')"
RUN_ID="${GITHUB_RUN_ID:-0}"
RUN_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
REPO="${GITHUB_REPOSITORY:-$(git remote get-url origin 2>/dev/null | sed -E 's#.*[:/](.+/.+)\.git$#\1#' || echo unknown)}"
COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"

SIG_ALG="none"
SIG_B64=""

# Optional local signing; on Windows this is flaky, so default is SKIP_SIGN=1
if [ "${SKIP_SIGN:-0}" != "1" ]; then
  SK=".tau_ledger/ed25519_sk.pem"
  PK=".tau_ledger/ed25519_pub.pem"
  if [ -n "${ED25519_SK_B64:-}" ]; then
    (echo "$ED25519_SK_B64" | base64 -d > "$SK") 2>/dev/null || (echo "$ED25519_SK_B64" | base64 -D > "$SK") || true
  else
    openssl genpkey -algorithm Ed25519 -out "$SK" 2>/dev/null || true
  fi
  if [ -s "$SK" ]; then
    chmod 600 "$SK"
    openssl pkey -in "$SK" -pubout -out "$PK" 2>/dev/null || true
    MSG="$(mktemp)"; trap 'rm -f "$MSG"' EXIT
    printf '{ "version":"tlog-1","timestamp":"%s","repo":"%s","commit":"%s","run_id":"%s","receipt_blake3":"%s","statement_blake3":"%s" }' \
      "$RUN_TS" "$REPO" "$COMMIT" "$RUN_ID" "$R_HASH" "$S_HASH" > "$MSG"
    SIG_BIN="$(mktemp)"
    if openssl pkeyutl -sign -inkey "$SK" -in "$MSG" -out "$SIG_BIN" 2>/dev/null; then
      SIG_B64="$(base64 -w0 "$SIG_BIN" 2>/dev/null || base64 "$SIG_BIN" | tr -d '\n')"
      SIG_ALG="ed25519/openssl"
    fi
    rm -f "$SIG_BIN"
  fi
fi

printf '{ "version":"tlog-1","timestamp":"%s","repo":"%s","commit":"%s","run_id":"%s","receipt_blake3":"%s","statement_blake3":"%s","sig_b64":"%s","sig_alg":"%s" }\n' \
  "$RUN_TS" "$REPO" "$COMMIT" "$RUN_ID" "$R_HASH" "$S_HASH" "$SIG_B64" "$SIG_ALG" >> .tau_ledger/tlog.ndjson

echo "[ok] appended .tau_ledger/tlog.ndjson"
