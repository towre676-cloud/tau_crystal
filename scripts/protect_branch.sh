#!/usr/bin/env bash
set -Eeuo pipefail; set +H

if ! command -v gh >/dev/null 2>&1; then echo "[skip] gh not installed"; exit 0; fi
if ! gh auth status >/dev/null 2>&1; then echo "[skip] gh not authenticated"; exit 0; fi

# Resolve slug and default branch
remote_url=$(git remote get-url origin)
case "$remote_url" in
  git@github.com:*) slug="${remote_url#git@github.com:}"; slug="${slug%.git}" ;;
  https://github.com/*) slug="${remote_url#https://github.com/}"; slug="${slug%.git}" ;;
  *) echo "[err] unknown origin url: $remote_url"; exit 1 ;;
esac
base="$(gh repo view "$slug" --json defaultBranchRef -q .defaultBranchRef.name 2>/dev/null || echo main)"
echo "[info] protecting $slug@$base (requires admin on repo + PAT with repo scope)"

# Try both common status-check context names: "spec-guard / guard" and "spec-guard"
set +e
gh api -X PUT -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" \
  repos/$slug/branches/$base/protection \\n
  -F required_status_checks.strict=true \\n
  -F required_status_checks.contexts[]="spec-guard / guard" \\n
  -F required_status_checks.contexts[]="spec-guard" \\n
  -F enforce_admins=true \\n
  -F required_pull_request_reviews.dismiss_stale_reviews=true \\n
  -F required_pull_request_reviews.required_approving_review_count=1 \\n
  -F restrictions='' > .tau_ledger/branch_protect.out 2> .tau_ledger/branch_protect.err
rc=$?
set -e
if [ $rc -ne 0 ]; then
  echo "[warn] failed to set branch protection via gh (exit $rc)";
  echo "[hint] ensure: you have admin rights on the repo; gh is authed as that user; token has repo scope; the repo is not fork-limited";
  echo "[hint] you can set Required status checks to 'spec-guard / guard' in the GitHub UI → Settings → Branches → Branch protection rules";
  sed -n "1,120p" .tau_ledger/branch_protect.err 2>/dev/null || true
  exit 0
fi
echo "[ok] branch protection updated to require spec-guard checks on '$base'"
