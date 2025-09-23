#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
scripts/fermion/build_receipts.sh
sha256sum analysis/fermion/fermion.receipt.json
