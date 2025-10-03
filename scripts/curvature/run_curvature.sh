#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
python3 scripts/curvature/_compute_cocycle.py
