#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
man="docs/manifest.md"
m=$(ls -1 .tau_ledger/mirror/mirrorv1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$m" ] || { echo "[skip] no mirror meta"; exit 0; }
id=$(basename "${m%.meta}")
sha=$(sha256sum "$m" | awk '{print $1}')
[ -f "$man" ] || : > "$man"
{
  printf '## mirror (v1)\n\n'
  printf 'id: %s\n' "$id"
  printf 'sha256: %s\n\n' "$sha"
} >> "$man"
echo "[OK] stamped mirror"
