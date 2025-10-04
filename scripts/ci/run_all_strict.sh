#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022
scripts/tools/py.sh scripts/proofs/emit_witnesses.py
scripts/ci/guard_proofs.sh
echo "[ok] CI proofs guard passed"
