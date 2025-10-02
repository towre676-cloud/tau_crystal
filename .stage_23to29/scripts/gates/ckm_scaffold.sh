#!/usr/bin/env bash
set -euo pipefail; umask 022
out="analysis/fermion/ckm.tsv"; mkdir -p "$(dirname "$out")"
{
  echo -e "# placeholder CKM (identity) — replace with fitted values"
  echo -e "1\t0\t0"
  echo -e "0\t1\t0"
  echo -e "0\t0\t1"
} > "$out"
echo "[CKM] scaffolded $out (will FAIL until replaced or ALLOW_PLACEHOLDER=1)"
