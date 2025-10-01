#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LED=".tau_ledger/freed"; mkdir -p "$LED"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
J="$LED/tmf_sigma_${STAMP}.json"; C="$LED/tmf_sigma_qleg_${STAMP}.csv"
python scripts/freed/tmf_qleg_emit.py "$J" "$C"
echo "[tmf] σ-orientation (q-leg) → $J"; head -n 6 "$C" || true
