#!/usr/bin/env bash
set -euo pipefail
cnt=$(ls -1 manifests/*.json 2>/dev/null | wc -l | tr -d " ")
echo "[verify] manifests = $cnt"
exit 0
