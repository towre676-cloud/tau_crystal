#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
fail=0
ALLOW_DIRTY=${FORENSICS_ALLOW_DIRTY:-0}
ALLOW_UNPUSHED=${FORENSICS_ALLOW_UNPUSHED:-0}
MAX_GHOSTS=${FORENSICS_GHOSTS_MAX:-100}
ALLOW_FILE=.gitignore.guard_allow; touch "$ALLOW_FILE"
if git status --porcelain=v1 | grep -q "^[MARCDUT]"; then if [ "$ALLOW_DIRTY" != "1" ]; then echo "[FORENSICS] working tree dirty"; fail=1; else echo "[FORENSICS] allowing dirty tree (override)"; fi; else echo "[FORENSICS] clean working tree"; fi
git fetch -q origin || true
BR=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)
if ! git diff --quiet HEAD "origin/$BR" 2>/dev/null; then if [ "$ALLOW_UNPUSHED" != "1" ]; then echo "[FORENSICS] unpushed commits present"; fail=1; else echo "[FORENSICS] allowing unpushed commits (override)"; fi; else echo "[FORENSICS] no unpushed commits"; fi
ghosts=$(git ls-files --others --exclude-standard | LC_ALL=C sort)
if [ -s "$ALLOW_FILE" ]; then ghosts=$(printf "%s\n" "$ghosts" | grep -v -f "$ALLOW_FILE" || true); fi
ghosts_n=$(printf "%s\n" "$ghosts" | sed "/^$/d" | wc -l | awk "{print \$1}")
if [ "${ghosts_n:-0}" -gt "$MAX_GHOSTS" ]; then echo "[FORENSICS] too many untracked files: $ghosts_n (max=$MAX_GHOSTS)"; fail=1; else echo "[FORENSICS] ghosts=$ghosts_n ok (max=$MAX_GHOSTS)"; fi
exit $fail
