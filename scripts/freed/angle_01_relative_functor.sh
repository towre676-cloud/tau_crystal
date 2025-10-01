#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
A="${1:-$(ls -1 analysis/freed/logB_segment_*_a.json 2>/dev/null | tail -n1)}"
B="${2:-$(ls -1 analysis/freed/logB_segment_*_b.json 2>/dev/null | tail -n1)}"
WHOLE="${3:-$(ls -1 analysis/freed/logB_segment_*_whole.json 2>/dev/null | tail -n1)}"
REL_TOL="${REL_TOL:-1e-9}"
for p in "$A" "$B" "$WHOLE"; do [ -s "${p:-}" ] || { echo "[err] missing segment/whole logB: $p"; exit 66; }; done
scripts/freed/angle_01_relative_functor.py "$A" "$B" "$WHOLE" "$REL_TOL"
