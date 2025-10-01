#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
bash scripts/meta/capsule_index.sh
bash scripts/meta/capsule_seal_set.sh
bash scripts/meta/build_descent_chain.sh
bash scripts/meta/bind_corridor_receipt.sh
[ -s docs/ledger/corridor_receipt.json ] || { echo "[gate] missing corridor receipt"; exit 64; }
grep -q "\"build_ok\":0" .tau_ledger/lean_module_capsules/index.json && { echo "[gate] FAIL: capsules failing"; exit 66; } || echo "[gate] OK: capsules healthy"
