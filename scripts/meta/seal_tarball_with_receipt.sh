#!/usr/bin/env bash
# seal_tarball_with_receipt — append a zero-byte τ marker into .tgz/.tar.gz
set -Eeuo pipefail; set +H; umask 022
usage(){ echo "usage: $0 <tarball.tgz|tar.gz> [witness.json]"; exit 2; }
tb="${1:-}"; [ -n "$tb" ] && [ -f "$tb" ] || usage
wit="${2:-}"
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
[ -n "$wit" ] || wit="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
[ -n "$wit" ] || wit="$(pick .tau_ledger/entropy/entv1-*.json)"
[ -n "$wit" ] || wit="$(pick .tau_ledger/receipts/*.json)"
if [ -z "$wit" ] || [ ! -s "$wit" ]; then
  [ -s .tau_ledger/CHAIN ] || { echo "[ERR] no witness/CHAIN"; exit 2; }
  mkdir -p .tau_ledger/tmp; wit=".tau_ledger/tmp/chain-witness.json"
  ch=$(sha .tau_ledger/CHAIN); : > "$wit"
  printf "%s\n" "{" >> "$wit"
  printf "%s\n" "\"schema\":\"taucrystal/chain_witness/v1\"," >> "$wit"
  printf "%s\n" "\"utc\":\"$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)\"," >> "$wit"
  printf "%s\n" "\"chain_sha256\":\"$ch\"" >> "$wit"
  printf "%s\n" "}" >> "$wit"
fi
H=$(sha "$wit")
case "$tb" in *.tgz|*.tar.gz) ;; *) echo "[ERR] not a .tgz/.tar.gz: $tb"; exit 2;; esac
work=$(mktemp -d); trap "rm -rf \"$work\"" EXIT
raw="$work/pkg.tar"; gzip -dc "$tb" > "$raw"
touch "$work/.tau-receipt.sha256-$H"
TZ=UTC LC_ALL=C tar --owner=0 --group=0 --numeric-owner --format=ustar --mtime="@0" -rf "$raw" -C "$work" ".tau-receipt.sha256-$H"
gzip -n -9 < "$raw" > "$work/out.tgz"
mv "$work/out.tgz" "$tb"
man="docs/manifest.md"; tmp="docs/.manifest.seal.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## sealed_tarball (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp";; esac; done < "$man"
printf "%s\n\n" "## sealed_tarball (v1)" >> "$tmp"
printf "%s\n" "artifact: $tb" >> "$tmp"
printf "%s\n" "witness: $wit" >> "$tmp"
printf "%s\n\n" "marker: .tau-receipt.sha256-$H" >> "$tmp"
mv "$tmp" "$man"
echo "[OK] sealed: $tb  (+ .tau-receipt.sha256-$H)"
