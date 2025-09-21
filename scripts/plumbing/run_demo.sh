#!/usr/bin/env bash
set +H
set -e
. scripts/plumbing/_lib.sh || exit 1
BOX="${1:-box-CM-D23}"
D="${2:--23}"; N="${3:-1}"
scripts/plumbing/box_build.sh "$BOX" "$D" "$N"
scripts/plumbing/hysteresis_loop.sh "$BOX" 96 1.0 0.07 0.0 0
for p in 3 5 23; do scripts/plumbing/hysteresis_prime.sh "$BOX" "$p" 96 0.02 0.0 0; done
scripts/plumbing/theta_lift.sh "$BOX" "$BOX" 1
scripts/plumbing/framing_phase.sh "$BOX" 1
scripts/plumbing/verify_hysteresis.sh "$BOX"
scripts/plumbing/receipt_emit.sh "$BOX" "cm-sector"
log "run_demo: complete for $BOX"
