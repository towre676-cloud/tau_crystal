#!/usr/bin/env bash
# lines: 60
# Repack a .tgz to include a zero-byte marker: .tau-receipt.sha256-<hash>
set -Eeuo pipefail; set +H; umask 022
tb="${1:-}"; wit="${2:-}"
[ -n "$tb" ] && [ -f "$tb" ] || { echo "usage: $0 <tarball.tgz|tar.gz> [witness.json]" >&2; exit 2; }
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ scripts/meta/_sha256.sh "$1"; }
if [ -z "$wit" ]; then
  wit="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
  [ -n "$wit" ] || wit="$(pick .tau_ledger/entropy/entv1-*.json)"
  [ -n "$wit" ] || wit="$(pick .tau_ledger/receipts/*.json)"
fi
[ -s "$wit" ] || { echo "[ERR] no witness found" >&2; exit 2; }
H="$(sha "$wit")"; marker=".tau-receipt.sha256-$H"

work=".tau_ledger/.work/seal.$$"; rm -rf "$work"; mkdir -p "$work/src"
cp -p "$tb" "$work/in.tgz"
# extract
tar -C "$work/src" -xzf "$work/in.tgz"
# add marker
mkdir -p "$work/src/."
: > "$work/src/$marker"
# repack deterministically
out="${tb%.tgz}.sealed.tgz"
out="${out%.tar.gz}.sealed.tgz"
tar -C "$work/src" --sort=name --owner=0 --group=0 --numeric-owner -czf "$out" .
rm -rf "$work"
echo "[OK] sealed: $out  (+ $marker)"
