#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

DRY=0
while [ "${1:-}" = "--dry-run" ]; do DRY=1; shift; done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p .cache
STATE="scripts/timefold/state_pack.sh"
[ -f "$STATE" ] || { echo "[err] missing $STATE"; exit 66; }

# newest compare receipt (no pipelines; strict-mode safe)
latest_compare=""; { shopt -s nullglob; tsmax=0; for f in .tau_ledger/entropy/entropy_compare_*.json; do
  ts="$(stat -c %Y "$f" 2>/dev/null || stat -f %m "$f" 2>/dev/null || echo 0)";
  if [ "${ts:-0}" -gt "$tsmax" ]; then tsmax="$ts"; latest_compare="$f"; fi; done; shopt -u nullglob; }
[ -n "${latest_compare:-}" ] || { echo "[note] no entropy_compare receipt found; nothing to toggle"; exit 0; }

if grep -Fq "$latest_compare" "$STATE"; then
  echo "[toggle] found in $STATE -> REMOVE: $latest_compare"
  [ "$DRY" -eq 1 ] && { echo "[dry-run] no changes"; exit 0; }
  cp -f "$STATE" "$STATE.bak"
  awk -v pat="$latest_compare" 'index($0, pat)==0{print $0}' "$STATE" > .cache/_sp.clean && mv -f .cache/_sp.clean "$STATE"
  bash -n "$STATE"; echo "[ok] removed; backup at $STATE.bak"
else
  echo "[toggle] not in $STATE -> ADD: $latest_compare"
  [ "$DRY" -eq 1 ] && { echo "[dry-run] no changes"; exit 0; }
  cp -f "$STATE" "$STATE.bak"
  awk -v anchor=".tau_ledger/git/git_head.txt" -v path="$latest_compare" '
    BEGIN{done=0; q=34}
    { print; if(!done && index($0,anchor)>0){ printf "  %c%s%c\n", q, path, q; done=1 } }
    END{ if(!done) printf "  %c%s%c\n", q, path, q }
\' "$STATE" > .cache/_sp.ins && mv -f .cache/_sp.ins "$STATE"
  awk "{print}" "$STATE" > .cache/_lf && mv -f .cache/_lf "$STATE"
  bash -n "$STATE"; echo "[ok] added; backup at $STATE.bak"
fi
