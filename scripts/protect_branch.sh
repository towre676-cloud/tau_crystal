#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

if ! command -v gh >/dev/null 2>&1; then echo "[skip] gh not installed"; exit 0; fi
if ! gh auth status >/dev/null 2>&1; then echo "[skip] gh not authenticated"; exit 0; fi

remote_url=$(git remote get-url origin)
case "$remote_url" in
  git@github.com:*) slug="${remote_url#git@github.com:}"; slug="${slug%.git}" ;;
  https://github.com/*) slug="${remote_url#https://github.com/}"; slug="${slug%.git}" ;;
  *) echo "[err] unknown origin url: $remote_url"; exit 1 ;;
esac
base="$(gh repo view "$slug" --json defaultBranchRef -q .defaultBranchRef.name 2>/dev/null || echo main)"
echo "[info] protecting $slug@$base (requires admin + repo-scoped token)"

out=".tau_ledger/branch_protect.out"; err=".tau_ledger/branch_protect.err"; mkdir -p .tau_ledger
set +e
gh api -X PUT -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" "repos/$slug/branches/$base/protection" -f required_status_checks.strict=true -f required_status_checks.contexts[]="spec-guard / guard" -f required_status_checks.contexts[]="spec-guard" -f enforce_admins=true -f required_pull_request_reviews.dismiss_stale_reviews=true -f required_pull_request_reviews.required_approving_review_count=1 1>"$out" 2>"$err"
rc=$?
set -e
if [ $rc -ne 0 ]; then
  echo "[warn] failed to set branch protection via gh (exit $rc)";
  echo "[hint] ensure: admin rights on repo; gh authed as an admin; token has repo scope; repo not fork-restricted";
  echo "[hint] manual path: Settings → Branches → Branch protection → Require status checks → add 'spec-guard / guard'";
  sed -n "1,80p" "$err" 2>/dev/null || true; exit 0
fi
echo "[ok] branch protection updated to require spec-guard on $base"
