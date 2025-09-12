#!/usr/bin/env bash
set -Eeuo pipefail; set +H
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
NOW_EPOCH="$(date -u +%s)"
CUTOFF_EPOCH="$(( NOW_EPOCH - 30*24*3600 ))"
CUTOFF_ISO="$(date -u -r "$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || date -u -d "@$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ)"
Q='.[] | [ .number, .updatedAt, ((.statusCheckRollup // []) | map(select(.conclusion != null) | .conclusion) | join(",")) ] | @tsv'
gh pr list -R "$REPO" --state open -L 200 --json number,updatedAt,statusCheckRollup --jq "$Q" | while IFS=$'\t' read -r NUM UPDATED CONCS; do
  if [[ "$UPDATED" < "$CUTOFF_ISO" ]] && printf '%s' "$CONCS" | grep -Eq '(^|,)(FAILURE|TIMED_OUT|CANCELLED|ACTION_REQUIRED)(,|$)'; then
    printf '#%s stale+red since %s\n' "$NUM" "$UPDATED"
    if [[ "${DOIT:-0}" = "1" ]]; then
      gh pr comment -R "$REPO" "$NUM" --body 'Closing as stale with failing checks; please reopen after fixes.' || true
      gh pr close   -R "$REPO" "$NUM" --delete-branch || true
    fi
  fi
done
