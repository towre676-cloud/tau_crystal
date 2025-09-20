#!/usr/bin/env bash
set -euo pipefail
fail(){ echo "ERROR: $*"; exit 1; }

# If README (or other top docs) try to assert meaningful mapping, require a signed pass.
GREEDY=$(grep -RIn --exclude-dir=.git -E "meaningful mapping\s*:\s*true" || true)
if [ -n "$GREEDY" ]; then
  REP="analysis/validation/meaningfulness_report.json"
  [ -f "$REP" ] || fail "README claims 'meaningful mapping: true' but $REP is missing."
  # Minimal sanity: must contain overall:'pass' and a signature field
  jq -e '.overall=="pass" and (.signature|type=="string")' "$REP" >/dev/null 2>&1 \
    || fail "Claim requires .overall=='pass' and .signature in $REP"
  echo "Meaningfulness claim guarded by signed report: OK."
else
  echo "No meaningful-claim detected; instrument-only posture OK."
fi
