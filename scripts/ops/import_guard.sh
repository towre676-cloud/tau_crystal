#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
graph="analysis/import-graph.tsv"
reasons="analysis/import-reasons.tsv"
[ -f "$graph" ]   || { mkdir -p analysis; printf "from\tto\n" > "$graph"; }
[ -f "$reasons" ] || { mkdir -p analysis; printf "from\tto\treason\n" > "$reasons"; }
tmp="$(mktemp)"; printf "from\tto\n" > "$tmp"
git ls-files "*.lean" "*.py" "*.sh" 2>/dev/null | while IFS= read -r f; do
  if printf "%s\n" "$f" | grep -qE "\.lean$"; then
    awk -v file="$f" '/^import /{gsub(/\r/,""); if(NF>=2){print file "\t" $2}}' "$f" >> "$tmp"
  else
    awk -v file="$f" '/^# import:/{gsub(/\r/,""); if(NF>=3){print file "\t" $3}}' "$f" >> "$tmp"
  fi
done
