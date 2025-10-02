#!/usr/bin/env bash
set -euo pipefail; set +H
PY=$(command -v python3 || true)
[ -x "$PY" ] || { echo 'python3 not found'; exit 1; }
exec "$PY" scripts/flow/two_loop_solver.py "$@"
