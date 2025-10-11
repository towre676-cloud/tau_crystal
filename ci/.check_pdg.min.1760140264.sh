#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
v=$(sed -n 's/.*"v"[[:space:]]*:[[:space:]]*\([0-9.eE+-]\+\).*/\1/p' tau_crystal/data/pdg/constants.json | tail -1)
sv=$(head -1 obstruction_card/out/singular_values_M.csv 2>/dev/null | tr -d '\r')
echo "== PDG gate (print-only) ==" 
if [ -n "${sv:-}" ] && [ -n "${v:-}" ]; then
  echo "-- Yukawa mass spectrum m_i = σ_i * v  (v=$v) --"
