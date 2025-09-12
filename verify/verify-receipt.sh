#!/usr/bin/env bash
# usage: verify/verify-receipt.sh <receipt.json> <expected_chain_head> <expected_merkle_root>
set -Eeuo pipefail; set +H; umask 022
rcpt="${1:?missing receipt}"; want_head="${2:?missing head}"; want_root="${3:?missing root}"
[ -s "$rcpt" ] || { echo "[ERR] receipt missing: $rcpt"; exit 2; }
calc="$(sha256sum "$rcpt" | awk '{print $1}')"
[ "$calc" = "$want_head" ] || { echo "[ERR] chain head mismatch"; exit 3; }
if command -v jq >/dev/null 2>&1; then
  got_root="$(jq -r '.reflective.merkle_root // .merkle_root // empty' "$rcpt")"
else
  got_root="$(grep -oE '"(reflective\.)?merkle_root"[[:space:]]*:[[:space:]]*"[^"]*"' "$rcpt" | head -n1 | sed -E 's/.*"([^"]*)".*/\1/')"
fi
[ -n "$got_root" ] || { echo "[ERR] could not read merkle_root from receipt"; exit 4; }
[ "$got_root" = "$want_root" ] || { echo "[ERR] merkle_root mismatch"; exit 5; }
# basic JSON sanity if jq is available
if command -v jq >/dev/null 2>&1; then jq empty "$rcpt" >/dev/null; fi
echo "[OK] receipt verified"
