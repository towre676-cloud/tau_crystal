#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
raw_out=$(python scripts/experimental/fft_bsd.py)
python scripts/experimental/_stamp_provenance.py "$raw_out" || true
echo "$raw_out"
