#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; else shasum -a 256 "$1" | awk '{print $1}'; fi; }
fail(){ echo "[replay] $*" >&2; exit 8; }
PACK="${1:-}"
if [ -z "$PACK" ]; then
  [ -s .tau_ledger/discovery/WITNESS_CHAIN ] || fail "no WITNESS_CHAIN"
  PACK=$(awk 'END{print $2}' .tau_ledger/discovery/WITNESS_CHAIN)
fi
[ -f "$PACK" ] || fail "pack not found: $PACK"
pack_sha=$(sha "$PACK")
if [ -s .tau_ledger/discovery/WITNESS_CHAIN ]; then
  expect=$(awk -v p="$PACK" '$2==p{print $1}' .tau_ledger/discovery/WITNESS_CHAIN | tail -n1)
  [ -n "$expect" ] || fail "pack not recorded in WITNESS_CHAIN: $PACK"
  [ "$expect" = "$pack_sha" ] || fail "pack sha mismatch: $pack_sha != $expect"
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
tar -xzf "$PACK" -C "$tmp"
REC="$tmp/discovery/receipt.json"; [ -s "$REC" ] || fail "missing receipt.json in pack"
rec_sha=$(sha "$REC")
chain_last=$(tail -n1 .tau_ledger/CHAIN); [ -n "$chain_last" ] || fail "empty CHAIN"
chain_sha=$(awk '{print $1}' <<<"$chain_last")
[ "$rec_sha" = "$chain_sha" ] || fail "receipt sha != CHAIN head: $rec_sha != $chain_sha"
if [ -x ./tau_verify ]; then ./tau_verify . >/dev/null || fail "tau_verify failed on repo"; fi
echo "[replay] OK (pack↔WITNESS_CHAIN, receipt↔CHAIN, verifier OK if present)"
