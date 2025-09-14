#!/usr/bin/env bash
# qr_witness.sh — zero‑dep, deterministic SVG hash badge + manifest stamp
set -Eeuo pipefail; set +H; umask 022
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
WITNESS="${1:-}"
[ -n "$WITNESS" ] || WITNESS="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
[ -n "$WITNESS" ] || WITNESS="$(pick .tau_ledger/entropy/entv1-*.json)"
[ -n "$WITNESS" ] || WITNESS="$(pick .tau_ledger/receipts/*.json)"
[ -n "$WITNESS" ] || WITNESS=".tau_ledger/CHAIN"
[ -s "$WITNESS" ] || { echo "[ERR] witness not found"; exit 1; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
HASH="$(sha "$WITNESS")"
SVG=".tau_ledger/qr/qr-witness.svg"; mkdir -p "$(dirname "$SVG")"
: > "$SVG"
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"640\" height=\"160\" viewBox=\"0 0 640 160\">" >> "$SVG"
printf "%s\n" "  <rect x=\"0\" y=\"0\" width=\"640\" height=\"160\" fill=\"#ffffff\" stroke=\"#000000\"/>" >> "$SVG"
printf "%s\n" "  <text x=\"20\" y=\"95\" font-family=\"monospace\" font-size=\"20\">witness sha256: $HASH</text>" >> "$SVG"
printf "%s\n" "</svg>" >> "$SVG"
man="docs/manifest.md"; tmpm="docs/.manifest.qr.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## qr_witness (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\n" "## qr_witness (v1)" >> "$tmpm"
printf "%s\n" "" >> "$tmpm"
printf "%s\n" "witness_path: $WITNESS" >> "$tmpm"
printf "%s\n" "witness_sha256: $HASH" >> "$tmpm"
printf "%s\n" "svg_path: $SVG" >> "$tmpm"
printf "%s\n" "" >> "$tmpm"
mv "$tmpm" "$man"
echo "[OK] qr_witness badge → $SVG (sha256:$HASH)"
