set -Eeuo pipefail; set +H; umask 022
python scripts/discovery/confirm_double_zero.py
python scripts/experimental/stabilize_json.py
python scripts/discovery/report_double_zero.py || true
python scripts/experimental/force_witness_types.py || true
