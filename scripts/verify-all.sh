#!/usr/bin/env bash
set -u
cnt=$(ls -1 manifests/*.json 2>/dev/null | wc -l | tr -d " ")
echo "[verify] manifests = ${cnt:-0}"
exit 0
