#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
if scripts/capsules/verify.sh; then
  printf "capsules_verify\tok\t%s\t-\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  exit 0
else
  printf "capsules_verify\tfail\t-\t[CAPVERIFY] mismatch\n"
  exit 1
fi
