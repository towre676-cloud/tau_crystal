#!/usr/bin/env bash
set -Eeuo pipefail; set +H
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
DAYS="${DAYS:-30}"
NOW_EPOCH="$(date -u +%s)"
CUTOFF_EPOCH="$(( NOW_EPOCH - DAYS*24*3600 ))"
CUTOFF_ISO="$(date -u -r "$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || date -u -d "@$CUTOFF_EPOCH" +%Y-%m-%dT%H:%M:%SZ)"
SKIP_REGEX="(^|,)(keep-open|pinned|wip)(,|$)|do-not-close"
count=0
Q='.[] | [ .number, ((.statusCheckRollup // []) | map(select(.conclusion != null) | .conclusion) | join(",")) ] | @tsv'
gh pr list -R "$REPO" --state open -L 200 --json number,statusCheckRollup --jq "$Q" | while IFS=$'\t' read -r NUM CONCS; do
  if ! printf '%s' "$CONCS" | grep -Eq '(^|,)(FAILURE|TIMED_OUT|CANCELLED|ACTION_REQUIRED)(,|$)'; then continue; fi
  LAST_ISO=$(gh pr view -R "$REPO" "$NUM" --json commits,updatedAt --jq '.commits[-1].commit.committedDate // .updatedAt' 2>/dev/null || true)
  [ -n "$LAST_ISO" ] || continue
  LABELS=$(gh pr view -R "$REPO" "$NUM" --json labels --jq '([.labels[].name] // []) | join(",")' 2>/dev/null || true)
  if printf '%s' "$LABELS" | grep -Eqi "$SKIP_REGEX"; then printf '#%s skip (labels: %s)\n' "$NUM" "$LABELS"; continue; fi
  if [[ "$LAST_ISO" < "$CUTOFF_ISO" ]]; then
    printf '#%s stale-by-commit since %s (red)\n' "$NUM" "$LAST_ISO"
    count=$((count+1))
    if [[ "${DOIT:-0}" = "1" ]]; then
      gh pr comment -R "$REPO" "$NUM" --body "Closing as stale with failing checks (no commits in >= ${DAYS} days; last commit ${LAST_ISO}). Please reopen after fixes." || true
      gh pr close   -R "$REPO" "$NUM" --delete-branch || true
      sleep 0.2
    fi
  fi
done
[ "$count" -gt 0 ] || echo "[info] no red PRs meet the stale-by-commit threshold — nothing to close"
[ "$count" -gt 0 ] || echo "[info] no red PRs meet the stale-by-commit threshold — nothing to close"
