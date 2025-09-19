#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
lat="${1:-.tau_ledger/phys/lattice.json}"; export EPS="${EPS:-1e-6}"
[ -f "$lat" ] || { echo "[err] lattice JSON not found: $lat" >&2; exit 2; }
python "scripts/phys/_gap_guard.py" "$lat"
exit $?
