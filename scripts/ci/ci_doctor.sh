#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ok(){ printf "✅ %s\n" "$1"; }
warn(){ printf "⚠️  %s\n" "$1"; }
bad(){ printf "❌ %s\n" "$1"; }
sep(){ printf "----\n"; }
sep
printf "CI Doctor — basic repo checks\n"
sep
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then ok "inside a Git repo"; else bad "not inside a Git repo"; exit 2; fi
BR=$(git branch --show-current 2>/dev/null || echo "")
if [ -n "$BR" ]; then ok "current branch: $BR"; else bad "detached HEAD (CI will still run on push/PR, but be aware)"; fi
if git remote get-url origin >/dev/null 2>&1; then
  ORI=$(git remote get-url origin); ok "origin remote present: $ORI"
  case "$ORI" in
    *github.com* ) ok "remote points to GitHub";;
    * ) warn "remote is not GitHub; Actions only runs on GitHub repos";;
  esac
else bad "no origin remote set"; fi
sep
printf "workflows\n"
sep
WF_DIR=".github/workflows"
if [ -d "$WF_DIR" ]; then ok "found $WF_DIR"; else bad "missing $WF_DIR"; fi
mapfile -t WFS < <(find "$WF_DIR" -maxdepth 1 -type f \( -name "*.yml" -o -name "*.yaml" \) 2>/dev/null | LC_ALL=C sort)
if [ "${#WFS[@]}" -gt 0 ]; then
  ok "workflow files:"
  for w in "${WFS[@]}"; do printf "   • %s\n" "$w"; done
else bad "no *.yml or *.yaml under $WF_DIR"; fi
if command -v yamllint >/dev/null 2>&1; then
  err=0; for w in "${WFS[@]:-}"; do yamllint -d "{extends: default, rules: {line-length: disable}}" "$w" || err=1; done
  [ "$err" -eq 0 ] && ok "yamllint passed" || bad "yamllint found issues";
else warn "yamllint not installed; skipping YAML lint"; fi
sep
printf "triggers\n"
sep
LAST_MSG=$(git log -1 --pretty=%B 2>/dev/null || echo "")
case "$LAST_MSG" in *"[skip ci]"*|*"[ci skip]"* ) bad "last commit message contains [skip ci]";; * ) ok "last commit message does not skip CI";; esac
if git diff --quiet --name-only HEAD~1..HEAD -- .github/workflows 2>/dev/null; then
  warn "last commit may not have changed workflows (that is fine if you pushed other files)";
else ok "last commit touched a workflow file"; fi
if [ -n "${BR:-}" ] && git rev-parse "origin/$BR" >/dev/null 2>&1; then
  if git rev-list --left-right --count "origin/$BR...$BR" | awk "{print \$2}" | grep -q "^[1-9]"; then
    bad "local branch is ahead of origin/$BR (unpushed commits) → push to trigger CI"
  else ok "no unpushed commits on $BR"; fi
else warn "cannot compare to origin/$BR (branch missing on remote or detached)"; fi
sep
printf "permissions & repo settings (hints)\n"
sep
if [[ "${ORI:-}" == *github.com* ]]; then
  ok "Actions should be available — verify in: GitHub → Settings → Actions → General"
  printf "   • Ensure: Actions permissions = Allow all actions and reusable workflows\n"
  printf "   • If this is a fork/PR: a maintainer may need to approve first run\n"
fi
sep
printf "next steps (to force a run)\n"
sep
printf "   • Touch a file and push:\n"
printf "       date > .ci_ping && git add .ci_ping && git commit -m \"ci: ping\" && git push\n"
printf "   • Then open: GitHub → Actions tab → select your branch\n"
