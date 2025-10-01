#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
case "${1:-}" in
  phi)    bash scripts/freed/run_phi_checks.sh ;;
  tmf)    bash scripts/freed/run_tmf_sigma.sh ;;
  list)   ls -1 .tau_ledger/freed 2>/dev/null || true ;;
  preview)
    echo "[ledger] newest pullback receipt:"
    bash -O nullglob -c 'printf "%s\n" .tau_ledger/freed/phi_pullback_*.json' | sort | tail -n1 | xargs -r -I{} sh -c 'echo "{}"; sed -n "1,30p" "{}"'
    echo "[ledger] newest tmf sigma receipt and first rows of CSV:"
    bash -O nullglob -c 'printf "%s\n" .tau_ledger/freed/tmf_sigma_*.json' | sort | tail -n1 | xargs -r -I{} sh -c 'echo "{}"; sed -n "1,30p" "{}"'
    bash -O nullglob -c 'printf "%s\n" .tau_ledger/freed/tmf_sigma_E4_*.csv' | sort | tail -n1 | xargs -r -I{} sh -c 'echo "{}"; sed -n "1,10p" "{}"'
    ;;
  lean)   bash scripts/freed/lean_prove_and_stamp.sh ;;
  *) echo "usage: bash scripts/freed/run.sh {phi|tmf|list|preview|lean}"; exit 2 ;;
esac
