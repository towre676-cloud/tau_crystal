#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

# tau-phys-guards-begin
SOFT=1 EPS=${EPS:-1e-6} scripts/phys/spectral_gap_guard.sh .tau_ledger/phys/lattice.json || true
scripts/phys/debye_cap_from_lattice.sh .tau_ledger/phys/lattice.json .tau_ledger/phys/debye_cap.txt
HARD=0 scripts/lean/recursion_cap_guard.sh .tau_ledger/phys/debye_cap.txt src || true
# tau-phys-guards-end
