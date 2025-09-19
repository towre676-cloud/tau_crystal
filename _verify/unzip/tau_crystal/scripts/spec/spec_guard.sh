#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
grep -q "Proof-carrying runtime manifests" README.md || { echo "[spec] missing elevator"; exit 4; }
grep -q "^## Quick links" README.md || { echo "[spec] missing Quick links"; exit 4; }
for w in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$w" ] || continue
  case "$(basename "$w")" in assure.yml|panic-sentinel.yml) true ;; *) echo "[spec] root workflow forbidden: $w"; exit 5 ;; esac
done
echo "[ok] spec guard clean"
