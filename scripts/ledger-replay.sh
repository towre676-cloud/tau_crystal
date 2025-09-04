#!/usr/bin/env bash
set -euo pipefail
lake env lean --run FusionMain.lean >/dev/null
cmp --silent manifests/tau_fusion.json "$1" && echo "OK: identical" && exit 0 || {
  echo "DIFF: manifests/tau_fusion.json != $1"
  exit 2
}
