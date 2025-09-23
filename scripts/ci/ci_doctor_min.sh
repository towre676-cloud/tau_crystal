#!/usr/bin/env bash
# portable CI diagnostics; no yamllint, no emojis, no bashisms
set -u
fail=0; PING=0
while [ $# -gt 0 ]; do case "$1" in --ping) PING=1;; esac; shift; done
ok(){ printf "[OK]   %s\n" "$1"; }; warn(){ printf "[WARN] %s\n" "$1"; }; bad(){ printf "[FAIL] %s\n" "$1"; fail=1; }; sep(){ printf '----\n'; }

sep; printf "CI Doctor — basic repo checks\n"; sep
git rev-parse --is-inside-work-tree >/dev/null 2>&1 && ok "inside a Git repo" || { bad "not inside a Git repo"; exit 2; }
BR=$(git branch --show-current 2>/dev/null || printf "")
[ -n "$BR" ] && ok "current branch: $BR" || warn "detached HEAD (push/PR can still trigger CI)"

if git remote get-url origin >/dev/null 2>&1; then
  ORI=$(git remote get-url origin 2>/dev/null || printf "")
  ok "origin remote present: $ORI"
  echo "$ORI" | grep -qi github.com && ok "remote points to GitHub" || warn "remote isn't GitHub; Actions only runs on GitHub"
else bad "no origin remote set"; fi

sep; printf "workflows\n"; sep
WF_DIR=".github/workflows"; [ -d "$WF_DIR" ] && ok "found $WF_DIR" || bad "missing $WF_DIR"
WF_COUNT=0
for ext in yml yaml; do
  for w in $(find "$WF_DIR" -maxdepth 1 -type f -name "*.${ext}" 2>/dev/null | sort); do
    [ -n "$w" ] && { [ $WF_COUNT -eq 0 ] && ok "workflow files:"; printf "  - %s\n" "$w"; WF_COUNT=$((WF_COUNT+1)); }
  done
done
[ "$WF_COUNT" -gt 0 ] || bad "no *.yml or *.yaml under $WF_DIR"

sep; printf "triggers\n"; sep
MSG=$(git log -1 --pretty=%B 2>/dev/null || printf "")
case "$MSG" in *"[skip ci]"*|*"[ci skip]"* ) bad "last commit message contains [skip ci]";; * ) ok "last commit message does not skip CI";; esac
if [ -n "${BR:-}" ] && git rev-parse "origin/$BR" >/dev/null 2>&1; then
  AHEAD=$(git rev-list --left-right --count "origin/$BR...$BR" 2>/dev/null | awk '{print $2}')
  [ -n "$AHEAD" ] && [ "$AHEAD" -ge 1 ] && bad "ahead of origin/$BR by $AHEAD commit(s) → push" || ok "no unpushed commits on $BR"
else warn "cannot compare to origin/$BR (missing remote branch or detached)"; fi

sep; printf "permissions & repo settings (hints)\n"; sep
[ -n "${ORI:-}" ] && echo "$ORI" | grep -qi github.com && {
  ok "Check: GitHub → Settings → Actions → General"
  printf "   - Actions permissions = Allow\n"
  printf "   - Forks/PRs may require maintainer approval for first run\n"
}

if [ "$PING" -eq 1 ]; then
  if [ -z "${BR:-}" ]; then warn "--ping skipped (detached HEAD)"; else
    date > .ci_ping && git add .ci_ping >/dev/null 2>&1 || true
    git commit -m "ci: ping" >/dev/null 2>&1 || true
    git push -u origin "$BR" >/dev/null 2>&1 && ok "pushed .ci_ping to $BR" || bad "push failed"
  fi
fi

sep; [ "$fail" -eq 0 ] && { printf "CI Doctor finished with no blocking errors.\n"; exit 0; } || { printf "CI Doctor finished with failures (see [FAIL]).\n"; exit 1; }
