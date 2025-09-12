#!/usr/bin/env bash
set -Eeuo pipefail; set +H
F="${1:-}"; [ -f "$F" ] || { echo "usage: scripts/ci/validate_receipt.sh receipts/..json" >&2; exit 2; }
grep -Eq "\"schema\"[[:space:]]*:[[:space:]]*\"taucrystal/receipt/v1\"" "$F" || { echo "bad: schema"; exit 3; }
grep -Eq "\"tau_class\"[[:space:]]*:" "$F" || { echo "bad: tau_class"; exit 3; }
grep -Eq "\"params\"[[:space:]]*:\\{[[:space:]]*\"K\"[[:space:]]*:" "$F" || { echo "bad: params"; exit 3; }
grep -Eq "\"provenance\"[[:space:]]*:\\{[[:space:]]*\"git_commit\"[[:space:]]*:" "$F" || { echo "bad: provenance"; exit 3; }
grep -Eq "\"tau\"[[:space:]]*:\\[" "$F" || { echo "bad: tau"; exit 3; }
echo "ok: $F"
