#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
bash scripts/langlands/morse_analysis.sh || true
bash scripts/langlands/functional_equation.sh || true
bash scripts/langlands/ramanujan_bounds.sh || true
bash scripts/langlands/trace_formula.sh || true
bash scripts/langlands/endoscopy_scan.sh || true
bash scripts/langlands/padic_family.sh || true
bash scripts/langlands/deformation_ring.sh || true
