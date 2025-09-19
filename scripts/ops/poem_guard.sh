#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
msg=$(git log -1 --pretty=%B 2>/dev/null | tr -d "\r")
allow=$(printf "%s\n" "$msg" | grep -ci "^Poem-Change: allow" || true)
status=0
for p in poems/pm3m.txt poems/p6mm.txt; do
  [ -r "$p" ] || { echo "[poem] missing $p"; status=1; continue; }
done
[ "$status" -eq 0 ] || exit 6
[ "$allow" -gt 0 ] && { echo "[poem] change allowed by commit switch"; exit 0; }
prev=$(git rev-parse HEAD^ 2>/dev/null || true)
[ -n "$prev" ] || { echo "[poem] first commit or no parent; pass"; exit 0; }
git diff --name-only "$prev"...HEAD -- poems/ | grep -q . && { echo "[poem] poem files changed without Poem-Change: allow"; exit 7; }
echo "[poem] ok"
