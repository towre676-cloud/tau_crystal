#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
man="docs/manifest.md"
j=$(ls -1 .tau_ledger/holo/holov1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$j" ] || { echo "[skip] no holo json"; exit 0; }
id=$(basename "${j%.json}")
sha=$(sha256sum "$j" | awk '{print $1}')
[ -f "$man" ] || : > "$man"
{
  printf '## holo (v1)\n\n'
  printf 'id: %s\n' "$id"
  printf 'sha256: %s\n\n' "$sha"
} >> "$man"
echo "[OK] stamped holo"
