#!/usr/bin/env bash
set -euo pipefail
LOCK="analysis/geom/canonical_truths.lock"
DOC="analysis/geom/canonical_truths.txt"
ALLOW="${ALLOW_RECANONIZE:-false}"
[ -f "$LOCK" ] && [ -f "$DOC" ] || { echo "::error::missing lock or doc"; exit 1; }
locked=$(awk '$1=="HASH"{print $2}' "$LOCK")
cur=$(sha256sum "$DOC" | awk '{print $1}')
if [ "$cur" = "$locked" ]; then
  echo "Canonical truths hash OK: $cur"
  exit 0
fi
# detect override via commit message or env
commit_msg=$(git log -1 --pretty=%B 2>/dev/null || echo "")
if echo "$commit_msg" | grep -q "RECANONIZE=TRUE"; then ALLOW=true; fi
if [ "$ALLOW" = "true" ]; then
  echo "::warning::hash changed but RECANONIZE=TRUE present; bypassing guard"
  exit 0
fi
echo "::error::canonical_truths.txt hash changed! locked=$locked current=$cur"
echo "To intentionally update, run scripts/geom/update_canon_lock.sh and include RECANONIZE=TRUE in the commit message."
exit 1
