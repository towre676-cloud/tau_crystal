#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
grep -q "Proof-carrying runtime manifests" README.md || { echo "[spec] missing elevator pitch"; exit 4; }
grep -q "^## Quick links" README.md || { echo "[spec] missing Quick links"; exit 4; }
for w in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -s "$w" ] || continue
  if grep -Eq "warn[-_ ]?only: *true" "$w"; then echo "[spec] $w is warn-only; cordon it under labs/"; exit 5; fi
done
echo "[ok] spec guard"
