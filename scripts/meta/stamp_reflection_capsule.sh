#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022
RUN="$(ls -td run_* 2>/dev/null | head -n1)"
[ -z "$RUN" ] && { echo "[ERR] No capsule run found"; exit 1; }
cd "$RUN"
echo "[STAMP] Reflect capsule → $RUN"
sha256sum report.json > report.sha256
tar -czf capsule.tar.gz report.json entropy.csv manifest.txt report.sha256
echo "[DONE] Capsule sealed: $RUN/capsule.tar.gz"
