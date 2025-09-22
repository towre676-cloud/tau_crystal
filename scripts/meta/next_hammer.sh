#!/usr/bin/env bash
set -euo pipefail; umask 022
echo "=== NEXT hammer start ==="
bash scripts/meta/vows_stamp.sh
bash scripts/gates/phase_head_gate.sh || true
bash scripts/gates/ckm_unitary_gate.sh || true
# capsule the latest stabilized double-zero set
bash scripts/meta/capsule_families.sh "dz-$(date -u +%Y%m%dT%H%M%SZ)" || true
# enforce morpho boundaries
bash scripts/morpho/enforce_all_boundaries.sh || true
# provenance
[ -x scripts/meta/build_provenance_map.sh ] && bash scripts/meta/build_provenance_map.sh || true
# stamp a gates report if present
[ -x scripts/gates/gen_gates_report.sh ] && bash scripts/gates/gen_gates_report.sh || true
echo "=== NEXT hammer done ==="
