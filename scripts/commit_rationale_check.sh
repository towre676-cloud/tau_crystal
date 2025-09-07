#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
ENFORCE="${ENFORCE:-0}"
RANGE="${1:-HEAD~1..HEAD}"
summary(){ if [ -n "${GITHUB_STEP_SUMMARY:-}" ] && [ -w "$GITHUB_STEP_SUMMARY" ]; then printf "%s\n" "$*" >> "$GITHUB_STEP_SUMMARY" || true; fi; }
COMMITS="$(git rev-list "$RANGE" 2>/dev/null || true)"
if [ -z "$COMMITS" ]; then echo "[rationale] no commits in range $RANGE"; summary "Commit rationale: no commits in range. ✅"; exit 0; fi
missing=0; reviewed=0
for c in $COMMITS; do
  reviewed=$((reviewed+1))
  msg="$(git log -1 --pretty=%B "$c")"
  if printf "%s" "$msg" | grep -Eiq "(^|\\n)(why:|rationale:|because|motivation:|explain:)"; then
    echo "[rationale][ok]   $c ${msg%%$'\n'*}"
  else
    echo "[rationale][miss] $c ${msg%%$'\n'*}"
    missing=$((missing+1))
  fi
done
if [ "$missing" -gt 0 ]; then
  summary "### Commit rationale warnings\nChecked $reviewed commit(s); $missing missing a clear why/rationale. Add a line like \`rationale:\` or \`why:\` to future messages while the audit stabilizes."
  if [ "$ENFORCE" = "1" ]; then echo "[rationale] enforcement on; failing"; exit 1; else echo "[rationale] warn-only; passing"; exit 0; fi
else
  summary "Commit rationale: all commits include a why. ✅"
  exit 0
fi
