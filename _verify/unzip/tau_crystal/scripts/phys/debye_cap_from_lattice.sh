#!/usr/bin/env bash
set +H; umask 022
lat="${1:-.tau_ledger/phys/lattice.json}"
out="${2:-.tau_ledger/phys/debye_cap.txt}"
python scripts/phys/_debye_cap.py "$lat" "$out"
