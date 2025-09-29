#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
BASE=".tau_ledger/lean_module_capsules"; IDX="$BASE/index.json"; : > "$IDX"; printf "[" >> "$IDX"; sep=""
find "$BASE" -type f -name "*.json" ! -name "index.json" ! -name "capsule_set.seal.json" -print0 | sort -z | while IFS= read -r -d "" j; do printf "%s" "$sep" >> "$IDX"; cat "$j" >> "$IDX"; sep=","; done
printf "]\n" >> "$IDX"
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$IDX" > "$BASE/index.sha256"; else openssl dgst -sha256 "$IDX" | awk "{print \$2}" > "$BASE/index.sha256"; fi
