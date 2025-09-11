#!/usr/bin/env bash
set -Eeuo pipefail; set +H
command -v gh >/dev/null 2>&1 || { echo "[skip] gh not installed"; exit 0; }
owner_repo=$(git remote get-url origin)
case "$owner_repo" in
  git@github.com:*) slug="${owner_repo#git@github.com:}"; slug="${slug%.git}" ;;
  https://github.com/*) slug="${owner_repo#https://github.com/}"; slug="${slug%.git}" ;;
  *) echo "[err] unknown remote url: $owner_repo"; exit 1 ;;
esac
base=$(gh repo view --json defaultBranchRef -q .defaultBranchRef.name 2>/dev/null || echo main)
echo "[info] protecting: $slug@$base"
gh api -X PUT -H "Accept: application/vnd.github+json" \\
  repos/$slug/branches/$base/protection \\n
  -f required_status_checks.strict=true \\n
  -F required_status_checks.contexts[]=spec-guard \\n
  -F enforce_admins=true \\n
  -F required_pull_request_reviews.dismiss_stale_reviews=true \\n
  -F required_pull_request_reviews.required_approving_review_count=1 \\n
  -F restrictions=''\n
echo "[ok] branch protection updated (requires spec-guard)"; exit 0
