#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
echo "[phase-next] start  UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
if [ -x scripts/langlands/reciprocity_verify.sh ]; then
  bash scripts/langlands/reciprocity_verify.sh 1000 .tau_ledger .tau_ledger/demo || {
    [ -x scripts/langlands/theta_scan_wide.sh ] && bash scripts/langlands/theta_scan_wide.sh .tau_ledger .tau_ledger/demo || true
    [ -x scripts/langlands/reciprocity.sh ] && bash scripts/langlands/reciprocity.sh .tau_ledger .tau_ledger/demo 1000 || true
  }
fi
[ -x scripts/langlands/morse_analysis.sh ] && bash scripts/langlands/morse_analysis.sh || true
if [ -x scripts/langlands/functional_equation.sh ]; then
  [ -s analysis/double_zero_ords.tsv ] || { [ -x scripts/langlands/double_zero_scan.sh ] && bash scripts/langlands/double_zero_scan.sh || true; }
  bash scripts/langlands/functional_equation.sh || true
fi
[ -x scripts/langlands/ramanujan_bounds.sh ] && bash scripts/langlands/ramanujan_bounds.sh || true
[ -x scripts/langlands/trace_formula.sh ] && bash scripts/langlands/trace_formula.sh || true
[ -x scripts/langlands/endoscopy_scan.sh ] && bash scripts/langlands/endoscopy_scan.sh || true
[ -x scripts/langlands/padic_family.sh ] && bash scripts/langlands/padic_family.sh || true
[ -x scripts/langlands/deformation_ring.sh ] && bash scripts/langlands/deformation_ring.sh || true
[ -x scripts/langlands/generate_monograph.sh ] && bash scripts/langlands/generate_monograph.sh || true
[ -x scripts/langlands/update_ledger.sh ] && bash scripts/langlands/update_ledger.sh || true
echo "[phase-next] done    UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
