#!/usr/bin/env bash
set -euo pipefail
scripts/gates/chebyshev_moments.sh scripts/ops/cheby_example.ini | tee .cache/cheby_example.json
