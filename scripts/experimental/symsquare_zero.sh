#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
in_json="${1:-}"; [ -n "${in_json}" ] || { python - <<PY\nimport io\nprint(".tau_ledger/experimental/symsquare_zeros.json")\nPY\n exit 0; }
python scripts/experimental/symsquare_zero.py "$in_json"
