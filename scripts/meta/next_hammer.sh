#!/usr/bin/env bash
set -euo pipefail; umask 022

run_track () {
  local organ="$1"; shift
  local out; out="$(mktemp)"
  set +e; "$@" >"$out" 2>&1; local rc=$?; set -e
  if [ $rc -eq 0 ]; then
    bash scripts/meta/progress_update.sh "$organ" ok "-"
  else
    local err="$(grep -m1 -E '.+' "$out" | head -c 180 | tr '\t' ' ' )"
    [ -z "$err" ] && err="rc=$rc"
    bash scripts/meta/progress_update.sh "$organ" fail "$err"
  fi
  cat "$out"; rm -f "$out"
  return 0
}

echo "=== NEXT hammer start ==="
run_track vows        bash scripts/meta/vows_stamp.sh
# run the checks
run_track phasehead   bash scripts/gates/phase_head_gate.sh
run_track ckm         bash scripts/gates/ckm_unitary_gate.sh
# if either failed, auto‑fix and re‑check
grep -q '^phasehead\tfail' analysis/progress.tsv && run_track phasehead-fix bash scripts/gates/phase_head_fix.sh && run_track phasehead bash scripts/gates/phase_head_gate.sh
grep -q '^ckm\tfail'       analysis/progress.tsv && run_track ckm-fix       bash scripts/gates/ckm_scaffold.sh    && run_track ckm       bash scripts/gates/ckm_unitary_gate.sh

# capsule, boundaries, provenance, gates
run_track capsules    bash scripts/meta/capsule_families.sh "dz-$(date -u +%Y%m%dT%H%M%SZ)"
run_track morpho      bash scripts/morpho/enforce_all_boundaries.sh
[ -x scripts/meta/build_provenance_map.sh ] && run_track provenance bash scripts/meta/build_provenance_map.sh
[ -x scripts/gates/gen_gates_report.sh ]    && run_track gates      bash scripts/gates/gen_gates_report.sh

echo "=== NEXT hammer done ==="
echo; echo "=== Progress table ==="; bash scripts/meta/progress_print.sh || true
