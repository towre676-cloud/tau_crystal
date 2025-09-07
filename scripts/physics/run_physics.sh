#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
summary(){ if [ -n "${GITHUB_STEP_SUMMARY:-}" ] && [ -w "$GITHUB_STEP_SUMMARY" ]; then printf "%s\n" "$*" >> "$GITHUB_STEP_SUMMARY" || true; fi; }
python3 scripts/physics/passport_probe.py || true
L_MAX="${L_MAX:-2.0}" E_MAX="${E_MAX:-50.0}" M_MAX="${M_MAX:-}" EPS_MAX="${EPS_MAX:-1e-6}" TAU_STAR="${TAU_STAR:-12}"
L_MAX="$L_MAX" E_MAX="$E_MAX" M_MAX="$M_MAX" EPS_MAX="$EPS_MAX" TAU_STAR="$TAU_STAR" python3 scripts/physics/select_params.py
N="$(jq -r .selected.n .tau_ledger/physics/pre_cert.json 2>/dev/null || python3 - <<PY; import json; print(json.load(open(".tau_ledger/physics/pre_cert.json"))["selected"]["n"]) ; PY )"
K="$(jq -r .selected.k .tau_ledger/physics/pre_cert.json 2>/dev/null || python3 - <<PY; import json; print(json.load(open(".tau_ledger/physics/pre_cert.json"))["selected"]["k"]) ; PY )"
N="$N" K="$K" python3 scripts/physics/run_and_measure.py || true
python3 scripts/physics/check_physics.py || true
summary "### Physics selection
$(printf "pre: %s" "$(sed -n "1,40p" .tau_ledger/physics/pre_cert.json 2>/dev/null | head -n 20)")
$(printf "\\npost: %s" "$(sed -n "1,40p" .tau_ledger/physics/post_cert.json 2>/dev/null | head -n 20)")"
