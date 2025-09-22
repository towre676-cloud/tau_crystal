#!/usr/bin/env bash
# docker_receipt_label.sh — emit OCI label from a τ witness (file|dir|glob|auto)
set -Eeuo pipefail; set +H; umask 022

pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1;
      elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1;
      else openssl dgst -sha256 "$1" | awk '{print $2}'; fi; }

arg="${1:-}"

# Resolve the witness:
# - explicit file → use it
# - directory     → pick newest *.json inside
# - glob          → expand and pick newest
# - empty         → sheaf → entropy → receipts → synthesize from CHAIN
W=""
if [ -n "$arg" ]; then
  if [ -f "$arg" ]; then
    W="$arg"
  elif [ -d "$arg" ]; then
    W="$(pick "$arg"/*.json)"
  else
    # treat as glob
    W="$(pick $arg)"
  fi
fi

[ -n "$W" ] || W="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
[ -n "$W" ] || W="$(pick .tau_ledger/entropy/entv1-*.json)"
[ -n "$W" ] || W="$(pick .tau_ledger/receipts/*.json)"

if [ -z "$W" ] || [ ! -s "$W" ]; then
  if [ -s .tau_ledger/CHAIN ]; then
    mkdir -p .tau_ledger/qr
    W=".tau_ledger/qr/chain-witness.json"
    CH="$(sha .tau_ledger/CHAIN)"
    : > "$W"
    printf '%s\n' '{'                         >> "$W"
    printf '%s\n' '"schema":"taucrystal/chain_witness/v1",' >> "$W"
    printf '%s\n' "\"utc\":\"$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)\"," >> "$W"
    printf '%s\n' "\"chain_sha256\":\"$CH\""  >> "$W"
    printf '%s\n' '}'                         >> "$W"
  else
    echo "[ERR] no witness (file/dir/glob) and no CHAIN" >&2
    exit 2
  fi
fi

H="$(sha "$W")"
echo "org.opencontainers.image.source.receipt=sha256:$H"
