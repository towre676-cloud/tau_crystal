#!/usr/bin/env bash
# lines: 30
# Emit an OCI label that embeds a receipt hash.
set -Eeuo pipefail; set +H; umask 022
arg="${1:-}"
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ scripts/meta/_sha256.sh "$1"; }

choose(){
  local x="$1"
  if [ -z "$x" ]; then
    x="$(pick .tau_ledger/sheaf/*.json)"; [ -n "$x" ] || x="$(pick .tau_ledger/entropy/*.json)"
  elif [ -d "$x" ]; then
    x="$(pick "$x"/*.json)"
  else
    # allow globs
    set +e; local g; g=$(ls -1 $x 2>/dev/null | LC_ALL=C sort | tail -1); set -e
    [ -n "$g" ] && x="$g"
  fi
  echo "$x"
}

w="$(choose "$arg")"
[ -s "$w" ] || { echo "[ERR] no valid receipt in input" >&2; exit 2; }
H="$(sha "$w")"
echo "org.opencontainers.image.source.receipt=sha256:$H"
