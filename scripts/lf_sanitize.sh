#!/usr/bin/env bash
set -euo pipefail; set +H
for f in "$@"; do
  [ -f "$f" ] || continue
  tr -d '\r' < "$f" > "$f.tmp.$$" && mv -f "$f.tmp.$$" "$f"
done
