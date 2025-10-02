#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
PYBIN="${PYBIN:-python}"
command -v "$PYBIN" >/dev/null 2>&1 || PYBIN="python3"
command -v "$PYBIN" >/dev/null 2>&1 || { echo "[err] no python found"; exit 127; }
"$PYBIN" scripts/ci/py/check_affine_rg.py
"$PYBIN" scripts/receipt/verify_receipt_digest.py || true
