#!/usr/bin/env bash
# verify_tarball_seal — check the τ marker is present and matches witness
set -Eeuo pipefail; set +H; umask 022
tb="${1:-}"; wit="${2:-}"; [ -n "$tb" ] && [ -f "$tb" ] || { echo "usage: $0 <tarball.tgz> [witness.json]"; exit 2; }
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
[ -n "$wit" ] || wit="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
[ -n "$wit" ] || wit="$(pick .tau_ledger/entropy/entv1-*.json)"
[ -n "$wit" ] || wit="$(pick .tau_ledger/receipts/*.json)"
[ -s "$wit" ] || { echo "[ERR] no witness found"; exit 2; }
H=$(sha "$wit")
if tar -tzf "$tb" | grep -q "^\.tau-receipt\.sha256-$H$"; then
  echo "[OK] seal verified on $tb (sha256:$H)"
else
  echo "[FAIL] seal missing or mismatched for $tb"; exit 1
fi
