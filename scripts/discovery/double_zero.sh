#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
raw_out=$(python scripts/discovery/double_zero_hunt.py)
python scripts/experimental/_stamp_provenance.py "$raw_out" || true
echo "$raw_out"
