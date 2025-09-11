#!/usr/bin/env bash
set -euo pipefail; set +H
[ -f analysis/tm1_sumrule.receipt.json ] && scripts/bin/emit_preimages.sh analysis/tm1_sumrule.receipt.json contracts/cp_residual_symm.tm1.contract.json request.tm1_sumrule.json || true
[ -f analysis/tm2_sumrule.receipt.json ] && scripts/bin/emit_preimages.sh analysis/tm2_sumrule.receipt.json contracts/cp_residual_symm.tm2.contract.json request.tm2_sumrule.json || true
