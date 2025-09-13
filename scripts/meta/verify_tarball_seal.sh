#!/usr/bin/env bash
# lines: 32
# Verify that a .tgz contains a matching receipt marker.
set -Eeuo pipefail; set +H; umask 022
tb="${1:-}"; wit="${2:-}"; [ -n "$tb" ] && [ -f "$tb" ] || { echo "usage: $0 <tarball.tgz> [witness.json]"; exit 2; }
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ scripts/meta/_sha256.sh "$1"; }
if [ -z "$wit" ]; then
  wit="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
  [ -n "$wit" ] || wit="$(pick .tau_ledger/entropy/entv1-*.json)"
  [ -n "$wit" ] || wit="$(pick .tau_ledger/receipts/*.json)"
fi
[ -s "$wit" ] || { echo "[ERR] no witness found"; exit 2; }
H="$(sha "$wit")"
if tar -tzf "$tb" | grep -qx "\.tau-receipt\.sha256-$H"; then
  echo "[OK] seal verified for $tb (sha256:$H)"
else
  echo "[FAIL] seal missing or mismatched for $tb"; exit 1
fi
