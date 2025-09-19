#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
man="docs/manifest.md"
f=$(ls -1 .tau_ledger/evolver/evolver-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$f" ] || { echo "[skip] no evolver json"; exit 0; }
id=$(basename "${f%.json}"); sha=$(sha256sum "$f" | awk '{print $1}')
[ -f "$man" ] || : > "$man"
printf '## evolver (v1)\n\nid: %s\nsha256: %s\n\n' "$id" "$sha" >> "$man"
echo "[OK] stamped evolver"
