#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
P1="${1:-$(ls -1 analysis/freed/logB_atlas_A_*.json 2>/dev/null | tail -n1)}"
P2="${2:-$(ls -1 analysis/freed/logB_atlas_B_*.json 2>/dev/null | tail -n1)}"
for p in "$P1" "$P2"; do [ -s "${p:-}" ] || { echo "[err] missing atlas logB: $p"; exit 66; }; done
scripts/freed/angle_03_atlas_swap.py "$P1" "$P2"
