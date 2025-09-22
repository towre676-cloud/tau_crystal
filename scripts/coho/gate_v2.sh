#!/usr/bin/env bash
set +e; set +H; umask 022
DL=".tau_ledger/delta.tsv"; TOL="${1:-${COHO_TOL:-0}}"
[ -f "$DL" ] || { echo "::error::missing $DL"; exit 1; }
L1=$(awk '{v=$2; if(v<0)v=-v; s+=v} END{print s+0}' "$DL")
if [ "${L1:-0}" -le "$TOL" ]; then echo "::notice::gate pass (|Δ|₁=$L1 ≤ tol=$TOL)"; exit 0; else echo "::error::gate fail (|Δ|₁=$L1 > tol=$TOL)"; exit 1; fi
