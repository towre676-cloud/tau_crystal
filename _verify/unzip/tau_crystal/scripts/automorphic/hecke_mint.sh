#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seed="${1:-$(date +%s)}"
python scripts/automorphic/hecke_mint.py "$seed"
