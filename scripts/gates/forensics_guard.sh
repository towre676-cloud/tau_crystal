#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
fail=0
if git status --porcelain=v1 | grep -q "^[MARCD]"; then echo "[FORENSICS] working tree dirty"; fail=1; fi
git fetch -q origin || true
if ! git diff --quiet HEAD origin/$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main) 2>/dev/null; then echo "[FORENSICS] unpushed commits present"; fail=1; fi
ghosts=$(git ls-files --others --exclude-standard | wc -l | awk "{print \$1}")
if [ "${ghosts:-0}" -gt 100 ]; then echo "[FORENSICS] too many untracked files: $ghosts"; fail=1; else echo "[FORENSICS] ghosts=$ghosts ok"; fi
exit $fail
