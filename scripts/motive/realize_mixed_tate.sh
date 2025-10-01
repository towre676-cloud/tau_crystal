#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:-MTM_affine_rg}"
MU0="${2:-1.0000000000}"
BPARM="${3:-0.1234567890}"
scripts/motive/new_mixed_tate.sh "$ID" "$MU0" "$BPARM" >/dev/null
scripts/motive/add_period.sh "$ID" Betti a_cycle "2.0000000000" >/dev/null
scripts/motive/add_period.sh "$ID" Betti b_cycle "3.0000000000" >/dev/null
scripts/motive/add_period.sh "$ID" deRham omega1  "2.0000000000" >/dev/null
scripts/motive/add_period.sh "$ID" deRham omega2  "3.0000000000" >/dev/null
scripts/motive/compare_bd.sh "$ID" >/dev/null
scripts/motive/init_regulator_stub.sh "$ID" >/dev/null
REC="$(scripts/motive/emit_receipt.sh "$ID")"
echo "[done] motive $ID realized; receipt: $REC"
