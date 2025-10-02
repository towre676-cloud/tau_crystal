#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
f="$1"; [ -f "$f" ] || { echo "[err] missing: $f"; exit 2; }
bash scripts/meta/capsule_one.sh "$f"
bash scripts/meta/capsule_index.sh
bash scripts/meta/capsule_seal_set.sh
bash scripts/docs/gen_module_catalog.sh || true
echo "[register] sealed and indexed: $f"
