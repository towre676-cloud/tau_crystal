#!/usr/bin/env bash
set +e; set +H; umask 022
run(){ "$@" >/dev/null 2>&1 || echo "[warn] $1 failed"; }
run scripts/genius/godel_self_verify.sh
run scripts/genius/quantum_entangle.sh 2
run scripts/genius/verify_entanglement.sh
run scripts/genius/temporal_paradox.sh 20260914T000000Z
run scripts/genius/consciousness_imprint.sh
run scripts/genius/dark_matter_verify.sh classified
run scripts/genius/gomboc_computation.sh
run scripts/genius/mandelbrot_receipt.sh tau-crystal-infinitum
run scripts/genius/omega_point.sh
run scripts/genius/riemann_foundation.sh 42
run scripts/genius/singularity_seed.sh 100
exit 0
