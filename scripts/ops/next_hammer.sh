#!/usr/bin/env bash
source scripts/ops/seed_init.sh
set -euo pipefail; umask 022
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# deterministic env
export LC_ALL=C
export PYTHONHASHSEED=0
[ -f .tau_env ] && . ./.tau_env

# default time limit per organ (seconds)
NEXT_TIMEOUT="${NEXT_TIMEOUT:-900}"

# run & capture canonical line
run_canon() {
  local organ="$1"; shift
  local ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  local buf rc
  buf="$(mktemp)"; rc=0
  set +e
  bash scripts/meta/timeout_run.sh "$NEXT_TIMEOUT" "$@" >"$buf" 2>&1
  rc=$?
  set -e
  local status="ok"; local err="-"
  if [ $rc -ne 0 ]; then
    status="fail"
    err="$(grep -m1 -E '.+' "$buf" | head -c 180 | tr '\t' ' ' )"
    [ -z "$err" ] && err="rc=$rc"
  fi
  echo "$organ	$status	$ts	$err"
  cat "$buf"
  rm -f "$buf"
  # update progress ledger
  bash scripts/meta/progress_update.sh "$organ" "$status" "$err"
  [ "$status" = "ok" ] || echo "[HAMMER] $organ failed" 1>&2
  return 0
}

echo "=== OPS hammer start ($(date -u +%Y-%m-%dT%H:%M:%SZ)) ==="

# 1) vows stamp (always runs)
run_canon vows        bash scripts/gates/vows_gate.sh

# 2) vows aging gate (new)
run_canon vows_age    bash scripts/gates/vows_age_gate.sh

# 3) phase head
run_canon phasehead   bash scripts/gates/phase_head_gate.sh

# 4) CKM unitary (placeholder ≠ pass)
run_canon ckm         bash scripts/gates/ckm_unitary_gate.sh

# 5) capsules (family builder + sealer)
run_canon capsules    bash scripts/meta/capsule_families.sh "auto-$(date -u +%Y%m%dT%H%M%SZ)"

# 6) morpho boundaries (scaffold -> FAIL by default)
run_canon morpho      bash scripts/morpho/enforce_all_boundaries.sh

# 7) provenance (optional)
[ -x scripts/meta/build_provenance_map.sh ] && run_canon provenance bash scripts/meta/build_provenance_map.sh || true

# 8) gates report (optional)
[ -x scripts/gates/gen_gates_report.sh ] && run_canon gates bash scripts/gates/gen_gates_report.sh || true

echo "=== OPS hammer end ($(date -u +%Y-%m-%dT%H:%M:%SZ)) ==="
echo; echo "=== Progress table ==="; bash scripts/meta/progress_print.sh || true

# hard-fail if any organ currently red
if grep -q -E '	fail	' analysis/progress.tsv; then
  echo "[OPS] one or more organs are red; exiting 1"
  exit 1
fi

# --- capsules verify (Merkle + boundary) ---
if bash scripts/gates/capsules_verify_gate.sh; then
  bash scripts/meta/progress_update.sh capsules_verify ok "-"
else
  bash scripts/meta/progress_update.sh capsules_verify fail "[CAPVERIFY] mismatch or boundary error"
fi
