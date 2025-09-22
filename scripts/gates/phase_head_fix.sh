#!/usr/bin/env bash
set -euo pipefail; umask 022
d=".tau_ledger/langlands"
latest="$d/phase_next_latest.sha"
[ -d "$d" ] || { echo "[PHASEFIX] missing $d"; exit 2; }
bestfile="$(LC_ALL=C ls "$d"/phase_next_*.sha 2>/dev/null | grep -v latest | sort -V | tail -n1 || true)"
[ -n "$bestfile" ] || { echo "[PHASEFIX] no phase_next_*.sha"; exit 3; }
bestbase="$(basename -- "$bestfile")"
ln -sf "$bestbase" "$latest"
echo "[PHASEFIX] linked $latest -> $bestbase"
