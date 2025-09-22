#!/usr/bin/env bash
set -e
LAKE="/c/Users/Cody/.elan/bin/lake.exe"
cd "$(dirname "$0")"

# ensure deps & build
"$LAKE" update >/dev/null || true
"$LAKE" build

# default args if you pass none
if [ $# -eq 0 ]; then
  RUN_ID="run-$(date +%Y%m%d-%H%M%S)"
  set -- --tau 1.25 --q "0.0,0.5,1.0,2.0" --run-id "$RUN_ID" --out "manifest.json" --audit true
fi

# run and preview manifest if present
"$LAKE" exe tau_crystal -- "$@"
echo
echo "Preview:"
head -n 1 manifest.json 2>/dev/null || true
