#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
REL_A="${REL_A:-$(ls -1 analysis/freed/logB_segment_*_a.json 2>/dev/null | tail -n1)}"
REL_B="${REL_B:-$(ls -1 analysis/freed/logB_segment_*_b.json 2>/dev/null | tail -n1)}"
REL_W="${REL_W:-$(ls -1 analysis/freed/logB_segment_*_whole.json 2>/dev/null | tail -n1)}"
echo "[a1] $(scripts/freed/angle_01_relative_functor.sh "$REL_A" "$REL_B" "$REL_W")"
echo "[a2] $(scripts/freed/angle_02_det_eta_curvature.py)"
if [ -x scripts/freed/angle_04_aps_split.sh ]; then echo "[a4] $(scripts/freed/angle_04_aps_split.sh)"; fi
AT_A="${AT_A:-$(ls -1 analysis/freed/logB_atlas_A_*.json 2>/dev/null | tail -n1)}"
AT_B="${AT_B:-$(ls -1 analysis/freed/logB_atlas_B_*.json 2>/dev/null | tail -n1)}"
echo "[a3] $(scripts/freed/angle_03_atlas_swap.sh "$AT_A" "$AT_B")"
echo "[a10] $(scripts/freed/angle_10_relative_index.py)"
