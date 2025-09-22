#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
fail=0
if git status --porcelain=v1 | grep -q "^[MARCD]"; then echo "[FORENSICS] working tree dirty"; fail=1; fi
git fetch -q origin || true
allow_unpushed=${FORENSICS_ALLOW_UNPUSHED:-0}
max_ghosts=${FORENSICS_GHOSTS_MAX:-100}
allow_file=.gitignore.guard_allow
touch "$allow_file"
if [ "$allow_unpushed" -ne 1 ]; then
  if ! git diff --quiet HEAD origin/$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main) 2>/dev/null; then echo "[FORENSICS] unpushed commits present"; fail=1; fi
else
  echo "[FORENSICS] allowing unpushed commits (override)"
fi
ghosts=$(git ls-files --others --exclude-standard | LC_ALL=C sort)
if [ -s "$allow_file" ]; then
  ghosts=$(printf "%s\n" "$ghosts" | grep -v -f "$allow_file" || true)
fi
ghosts_n=$(printf "%s\n" "$ghosts" | sed "/^$/d" | wc -l | awk "{print \$1}")
if [ "${ghosts_n:-0}" -gt "$max_ghosts" ]; then echo "[FORENSICS] too many untracked files: $ghosts_n (max=$max_ghosts)"; fail=1; else echo "[FORENSICS] ghosts=$ghosts_n ok (max=$max_ghosts)"; fi
if ! git diff --quiet HEAD origin/$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main) 2>/dev/null; then echo "[FORENSICS] unpushed commits present"; fail=1; fi
ghosts=$(git ls-files --others --exclude-standard | wc -l | awk "{print \$1}")
if [ "${ghosts:-0}" -gt 100 ]; then echo "[FORENSICS] too many untracked files: $ghosts"; fail=1; else echo "[FORENSICS] ghosts=$ghosts ok"; fi
exit $fail
