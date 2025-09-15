#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
out=$(python scripts/discovery/extract_ap_satake.py)
python scripts/experimental/_canonicalize_json.py "$out" || true
python scripts/experimental/_stamp_provenance.py "$out" || true
python scripts/experimental/_canonicalize_json.py "$out" || true
python scripts/experimental/_stamp_provenance.py ".tau_ledger/langlands/ap.json" || true
python scripts/experimental/_stamp_provenance.py ".tau_ledger/langlands/satake.json" || true
python scripts/discovery/validate_ap_satake.py "$out" || true
echo "$out"
