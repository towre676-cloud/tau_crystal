#!/usr/bin/env bash
# Robust orchestrator: never crash on guard failure; seal incident; proper rc
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set +e; set +u; set +H; umask 022

failures=()

run_step () {
  # Windows/NTFS: do not rely on -x; execute by existence
  # shellcheck disable=SC2164
  local name="$1"; shift
  if [ -f "$name" ]; then
    bash "$name" "$@"
    local s=$?
    if [ $s -ne 0 ]; then echo "[TRIP] $name exit=$s"; failures+=("$name:$s"); fi
  else
    echo "[WARN] missing step $name"
    ls -l "$name" 2>/dev/null || true
  fi
  return 0
}

# 1) thresholds verify (correct path!)
run_step scripts/meta/thresholds_verify.sh

# 2) provision baseline (noop if present)
run_step scripts/live/prepare_runtime_baseline.sh

# 3) guards
run_step scripts/live/guard_heegner_entropy.sh
run_step scripts/live/guard_virtualalloc_taint.sh
run_step scripts/ci/check_barcode_regression.sh

# 4) verdict + incident
if [ "${#failures[@]}" -gt 0 ]; then
  [ -x scripts/live/incident_capsule.sh ] && bash scripts/live/incident_capsule.sh || echo "[WARN] incident_capsule.sh missing"
  echo "[GUARD] verdict=FAIL rc=1 failures=${failures[*]}"; exit 1
else
  echo "[GUARD] verdict=PASS rc=0"; exit 0
fi
