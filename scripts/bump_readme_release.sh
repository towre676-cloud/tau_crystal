#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root"; exit 1; }
fail(){ printf "[FAIL] %s\n" "$1" >&2; exit 1; }
[ $# -eq 1 ] || fail "usage: scripts/bump_readme_release.sh vX.Y.Z"
new="$1"
[[ "$new" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([-.][0-9A-Za-z.]+)?$ ]] || fail "tag must look like v1.2.3 or v1.2.3-rc1"
files=(README.md docs/RELEASE_CHECKLIST.md docs/MARKETPLACE_AUDIT.md docs/marketplace-listing.md)
for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  tmp="$(mktemp)"
  awk -v new="$new" '/Verify this release|git checkout|^[#[:space:]]*Verify v/ { gsub(/v[0-9]+\.[0-9]+\.[0-9]+([-.][0-9A-Za-z.]+)?/, new) } { print }' "$f" > "$tmp"
  if ! cmp -s "$f" "$tmp"; then mv "$tmp" "$f"; echo "[bumped] $f -> $new"; else rm -f "$tmp"; fi
done
echo "[done] pinned snippets now reference: $new"
