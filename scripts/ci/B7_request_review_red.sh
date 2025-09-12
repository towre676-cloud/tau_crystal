#!/usr/bin/env bash
set -Eeuo pipefail; set +H
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
TARGET="${TARGET:-towre676-cloud}"; TARGET_CLEAN="${TARGET#@}"
Q='.[] | [ .number, ((.statusCheckRollup // []) | map(select(.conclusion != null) | .conclusion) | join(",")) ] | @tsv'
gh pr list -R "$REPO" --state open -L 200 --json number,statusCheckRollup --jq "$Q" | while IFS=$'\t' read -r NUM CONCS; do
  if printf '%s' "$CONCS" | grep -Eq '(^|,)(FAILURE|TIMED_OUT|CANCELLED|ACTION_REQUIRED)(,|$)'; then
    gh pr edit -R "$REPO" "$NUM" --add-reviewer "$TARGET_CLEAN" >/dev/null && printf '#%s -> requested %s\n' "$NUM" "$TARGET_CLEAN"
  fi
done
