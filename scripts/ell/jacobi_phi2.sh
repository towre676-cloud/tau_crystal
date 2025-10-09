#!/usr/bin/env bash
set -euo pipefail
ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] cd fail: $ROOT" >&2; exit 2; }
z="${1:?z}"; tau="${2:?tau}"; N="${3:-40}"
# normalize complex literals: allow 0.3+0.7i or 0.3+0.7j
case "$z"   in *[jJ]* ) ;; *[iI]* ) z="${z//I/i}"; z="${z//i/j}";; esac
case "$tau" in *[jJ]* ) ;; *[iI]* ) tau="${tau//I/i}"; tau="${tau//i/j}";; esac
exec python3 scripts/ell/jac_phi.py "$z" "$tau" "$N"
