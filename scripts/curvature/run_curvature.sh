#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022
scripts/tools/py.sh scripts/curvature/_compute_cocycle.py
