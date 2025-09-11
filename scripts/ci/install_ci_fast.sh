#!/usr/bin/env bash
set -Eeuo pipefail
dir="${1:?usage: install_ci_fast.sh <top-level-dir> <lang: python|rust|go|node>}"
lang="${2:?usage: install_ci_fast.sh <top-level-dir> <lang>}"
tmpl="scripts/ci/templates/Makefile.ci-fast.$lang"
[ -d "$dir" ] || { echo "[err] $dir not found"; exit 2; }
[ -f "$tmpl" ] || { echo "[err] template $tmpl not found"; exit 3; }

mf="$dir/Makefile"
touch "$mf"
if grep -qE '(^|[^#[:alnum:]_-])ci-fast\s*:' "$mf"; then
  echo "[skip] $dir already has ci-fast"
  exit 0
fi

echo "" >> "$mf"
echo "# --- added by scripts/ci/install_ci_fast.sh ---" >> "$mf"
cat "$tmpl" >> "$mf"
echo "[ok] installed ci-fast in $dir (lang=$lang)"
