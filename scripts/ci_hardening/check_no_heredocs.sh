#!/usr/bin/env bash
set -euo pipefail
set +H

# regex for any heredoc token (<<, <<-, optional backslash, optional quoted label)
p1='(^|[^<])'
p2='<<-?[[:space:]]*\\?'
p3='["'"'"']?[A-Za-z_][A-Za-z0-9_]*["'"'"']?'
pat="${p1}${p2}${p3}"

allow_file=".ci/heredoc.allow"
is_allowed(){ local f="$1"; [ -f "$allow_file" ] && grep -xFq -- "$f" "$allow_file"; }

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  mapfile -t files < <(git ls-files -- "*.sh")
else
  mapfile -t files < <(find . -type f -name "*.sh")
fi

viol=0
for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  if grep -nE "$pat" -- "$f" >/dev/null; then
    if ! is_allowed "$f"; then
      grep -nE "$pat" -- "$f" >&2 || true
      viol=1
    fi
  fi
done
exit "$viol"
