#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
passes_pad="120000 90000 60000 40000 25000 16000 10000"
passes_step="6000 4000 2000 1500 1000 800 600"
i=0; for pad in $passes_pad; do i=$((i+1)); step=$(echo $passes_step | awk -v n="$i" '{print $n}'); [ -z "$step" ] && step=1000
  echo "[live] pass $i pad=$pad step=$step"
  S_PAD="$pad" T_PAD="$pad" S_STEP="$step" T_STEP="$step" bash scripts/langlands/around_witness_scan.sh || true
  bash scripts/langlands/morse_analysis.sh || true
  bash scripts/langlands/seed_witness_envs.sh || true
  bash scripts/langlands/basins_map.sh || true
  bash scripts/langlands/atlas_line.sh || true
  bash scripts/langlands/update_ledger.sh || true
  scripts/meta/assure_push.sh || true
done
echo "[live] complete. you can re-run to go finer or widen the window."
