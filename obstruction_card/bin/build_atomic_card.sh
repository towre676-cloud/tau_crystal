#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
tmp=$(mktemp -d obstruction_card/tmp.XXXXXX)
python3 ledger/extract_window_96.py "$tmp"
python3 obstruction_card/bin/build_obstruction_card.py "$tmp"
mv "$tmp"/*.csv obstruction_card/out/ || { echo "atomic move failed"; exit 1; }
rmdir "$tmp"
