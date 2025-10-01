#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LED=".tau_ledger/freed"; mkdir -p "$LED"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"; J="$LED/tmf_sigma_$STAMP.json"; C="$LED/tmf_sigma_E4_$STAMP.csv"
python scripts/freed/tmf_sigma_emit.py "$J" "$C"
printf "%s\n" "[tmf] σ‑orientation receipt → $J"; head -n 5 "$C" 2>/dev/null || true
