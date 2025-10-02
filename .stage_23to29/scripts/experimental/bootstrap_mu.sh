#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
raw_out=$(python scripts/experimental/bootstrap_mu.py)
python scripts/experimental/_stamp_provenance.py "$raw_out" || true
echo "$raw_out"
