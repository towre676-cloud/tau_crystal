#!/usr/bin/env bash
set -Eeuo pipefail; set +H
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
DAYS="${DAYS:-30}"
NOW_EPOCH="$(date -u +%s)"
CUTOFF_EPOCH="$(( NOW_EPOCH - DAYS*24*3600 ))"
CUTOFF_ISO="$(date -u -r "$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || date -u -d "@$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ)"
SKIP_REGEX="(^|,)(keep-open|pinned|wip|do-not-close)(,|$)"
count=0
Q='.[] | [ .number, ((.statusCheckRollup // []) | map(select(.conclusion != null) | .conclusion) | join(",")) ] | @tsv'
gh pr list -R "$REPO" --state open -L 200 --json number,statusCheckRollup --jq "$Q" | while IFS=$'\t' read -r NUM CONCS; do
  if ! printf '%s' "$CONCS" | grep -Eq '(^|,)(FAILURE|TIMED_OUT|CANCELLED|ACTION_REQUIRED)(,|$)'; then continue; fi
  LAST_CHECK=$(gh pr view -R "$REPO" "$NUM" --json statusCheckRollup --jq '((.statusCheckRollup // []) | map(select(.completedAt != null) | .completedAt) | max) // ""' 2>/dev/null || true)
  [ -n "$LAST_CHECK" ] || continue
  LABELS=$(gh pr view -R "$REPO" "$NUM" --json labels --jq '([.labels[].name] // []) | join(",")' 2>/dev/null || true)
  if printf '%s' "$LABELS" | grep -Eqi "$SKIP_REGEX"; then printf '#%s skip (labels: %s)\n' "$NUM" "$LABELS"; continue; fi
  if [[ "$LAST_CHECK" < "$CUTOFF_ISO" ]]; then
    printf '#%s stale-by-check since %s (red)\n' "$NUM" "$LAST_CHECK"
    count=$((count+1))
    if [[ "${DOIT:-0}" = "1" ]]; then
      gh pr comment -R "$REPO" "$NUM" --body "Closing as stale with failing checks (no passing checks in >= ${DAYS} days; last check finished ${LAST_CHECK}). Please reopen after fixes." || true
      gh pr close   -R "$REPO" "$NUM" --delete-branch || true
      sleep 0.2
    fi
  fi
done
[ "$count" -gt 0 ] || echo "[info] no red PRs meet the stale-by-check threshold — nothing to close"
[ "$count" -gt 0 ] || echo "[info] no red PRs meet the stale-by-check threshold — nothing to close"
