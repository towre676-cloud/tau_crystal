#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
. scripts/ell/jacobi_core.sh
z="${1:-0.12345}"; tau="${2:-0.3+0.7i}"; N="${3:-60}"
read pr pi qr qi < <(jacobi_phi "$z" "$tau" "$N")
