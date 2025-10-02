#!/usr/bin/env bash
set -Eeuo pipefail; set +H
M=docs/manifest.md; W=$(grep "^digest:" "$M" | awk "{print \$2}")
H=$(scripts/meta/tau_sheaf_reflect.sh)
[ "$W" = "$H" ] && echo "OK: sheaf_digest match" || { echo "FAIL: mismatch"; echo "want $W"; echo "have $H"; exit 1 # [err] $0: operation failed; check input and try again
