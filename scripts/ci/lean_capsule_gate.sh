#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
IDX=".tau_ledger/lean_module_capsules/index.json"
[ -s "$IDX" ] || { echo "[gate] no index: $IDX"; exit 2; }
if grep -q "\"build_ok\":0" "$IDX"; then echo "[gate] FAIL: some modules failed cold capsule test"; exit 66; fi
echo "[gate] OK: all modules sealed and healthy"
