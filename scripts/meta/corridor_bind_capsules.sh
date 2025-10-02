#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
BASE=".tau_ledger/lean_module_capsules"; SEAL="$BASE/capsule_set.seal.json"; IDX="$BASE/index.json"
[ -s "$SEAL" ] || { echo "[err] missing seal: $SEAL"; exit 2; }
out="docs/ledger/lean_capsule_manifest.json"; : > "$out"
printf "{" >> "$out"
printf "\"kind\":\"corridor.manifest.lean_capsules\"," >> "$out"
printf "\"seal\":%s," "$(cat "$SEAL")" >> "$out"
printf "\"index_path\":\"%s\"" "$IDX" >> "$out"
printf "}\n" >> "$out"
