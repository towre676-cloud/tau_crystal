#!/usr/bin/env bash
set -e
mkdir -p .tau_ledger
MATHLIB_SHA="unknown"
if command -v jq >/dev/null 2>&1 && [ -f lake-manifest.json ]; then
  MATHLIB_SHA="$(jq -r '.packages[]|select(.name=="mathlib")|.rev // .git // "unknown"' lake-manifest.json 2>/dev/null || echo unknown)"
elif [ -x scripts/mathlib-sha.py ]; then MATHLIB_SHA="$(scripts/mathlib-sha.py 2>/dev/null || echo unknown)"; fi
LEAN_VER="$( (lean --version 2>/dev/null || echo unknown) | head -n1 )"
LAKE_VER="$( (lake --version 2>/dev/null || echo unknown) | head -n1 )"
OS="$(uname -s 2>/dev/null || echo unknown)"
EVENT="${GITHUB_EVENT_NAME:-unknown}"
RUN_ID="${GITHUB_RUN_ID:-0}"
WORKFLOW="${GITHUB_WORKFLOW:-unknown}"
JOB="${GITHUB_JOB:-unknown}"
BRANCH="${GITHUB_REF_NAME:-$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)}"
if [ -f /.dockerenv ]; then CONTAINER="container"; else CONTAINER="host"; fi
STRATEGY="${CI_CACHE_STRATEGY:-mathlib-only}"
JSON="{\"branch\":\"$BRANCH\",\"container\":\"$CONTAINER\",\"event\":\"$EVENT\",\"job\":\"$JOB\",\"lean\":\"$LEAN_VER\",\"lake\":\"$LAKE_VER\",\"mathlib_sha\":\"$MATHLIB_SHA\",\"os\":\"$OS\",\"run_id\":\"$RUN_ID\",\"strategy\":\"$STRATEGY\",\"workflow\":\"$WORKFLOW\"}"
printf "%s" "$JSON" > .tau_ledger/pattern.json
PATTERN_HASH="$(printf "%s" "$JSON" | sha256sum | awk "{print \$1}")"
printf "%s\n" "$PATTERN_HASH" > .tau_ledger/pattern.sha256
echo "[pattern] $PATTERN_HASH  ($STRATEGY / mathlib=$MATHLIB_SHA)"
