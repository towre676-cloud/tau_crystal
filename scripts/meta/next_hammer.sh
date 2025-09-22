#!/usr/bin/env bash
set -euo pipefail; umask 022

run_track () {
  local organ="$1"; shift
  local out; out="$(mktemp)"
  set +e
  "$@" >"$out" 2>&1
  local rc=$?
  set -e
  if [ $rc -eq 0 ]; then
    bash scripts/meta/progress_update.sh "$organ" ok "-"
  else
    # keep small, single-line error (first non-empty line)
    local err="$(grep -m1 -E '.+' "$out" | head -c 180 | tr '\t' ' ' )"
    [ -z "$err" ] && err="rc=$rc"
    bash scripts/meta/progress_update.sh "$organ" fail "$err"
  fi
  cat "$out"
  rm -f "$out"
  return 0  # hammer continues
}

echo "=== NEXT hammer start ==="
run_track vows        bash scripts/meta/vows_stamp.sh
run_track phasehead   bash scripts/gates/phase_head_gate.sh
run_track ckm         bash scripts/gates/ckm_unitary_gate.sh
run_track capsules    bash scripts/meta/capsule_families.sh "dz-$(date -u +%Y%m%dT%H%M%SZ)"
run_track morpho      bash scripts/morpho/enforce_all_boundaries.sh
if [ -x scripts/meta/build_provenance_map.sh ]; then
  run_track provenance bash scripts/meta/build_provenance_map.sh
fi
if [ -x scripts/gates/gen_gates_report.sh ]; then
  run_track gates      bash scripts/gates/gen_gates_report.sh
fi
echo "=== NEXT hammer done ==="
echo
echo "=== Progress table ==="
bash scripts/meta/progress_print.sh || true
