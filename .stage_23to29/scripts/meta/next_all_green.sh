#!/usr/bin/env bash
set -euo pipefail
bash scripts/gates/phase_head_fix.sh && bash scripts/gates/phase_head_gate.sh || true
bash scripts/gates/ckm_scaffold.sh     && bash scripts/gates/ckm_unitary_gate.sh || true
bash scripts/meta/next_hammer.sh
