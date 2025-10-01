#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
export LC_ALL=C LANG=C
LED=".tau_ledger/freed"; mkdir -p "$LED"

# 1) Produce receipts (tmf + PF/AGT/SW)
if [ -x scripts/freed/run_tmf_sigma.sh ]; then
  bash scripts/freed/run_tmf_sigma.sh
else
  echo "[err] missing scripts/freed/run_tmf_sigma.sh"; exit 2
fi
if [ -x scripts/freed/run_phi_checks.sh ]; then
  bash scripts/freed/run_phi_checks.sh
else
  echo "[err] missing scripts/freed/run_phi_checks.sh"; exit 2
fi

# 2) Stamp Lean build receipt (proof state)
if [ -x scripts/freed/lean_prove_and_stamp.sh ]; then
  bash scripts/freed/lean_prove_and_stamp.sh
else
  echo "[err] missing scripts/freed/lean_prove_and_stamp.sh"; exit 2
fi

# 3) Tag newest receipts with the current proof Merkle
need() { command -v "$1" >/dev/null 2>&1 || { echo "[err] missing tool: $1"; exit 1; }; }
need jq
LEAN=$(printf "%s\n" "$LED"/lean_build_*.json | LC_ALL=C sort | tail -n1)
MERKLE=$(jq -r '.olean_merkle' "$LEAN")
tag() { f="$1"; [ -f "$f" ] || return 0; tmp="$f.tmp.$$"; jq --arg m "$MERKLE" '.proof_build=$m' "$f" > "$tmp" && mv "$tmp" "$f" && echo "[tagged] $f"; }
tag "$(printf "%s\n" "$LED"/phi_pullback_*.json | LC_ALL=C sort | tail -n1)"
tag "$(printf "%s\n" "$LED"/tmf_sigma_*.json     | LC_ALL=C sort | tail -n1)"

# 4) Enforce CI guard locally
bash scripts/freed/ci_guard.sh
