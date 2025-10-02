#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
pack="${1:-}"; [ -n "$pack" ] || { echo "usage: $0 analysis/morpho/packs/run_xx"; exit 1; }
b="$pack/boundary.txt"; s="$pack/boundary.sig";
[ -f "$b" ] || { echo "[BOUNDARY] missing $b"; exit 2; }
bs=$(sha256sum "$b" | awk "{print \$1}")
if [ -f "$s" ]; then
  read -r ss < "$s" || ss=""
  [ "$ss" = "$bs" ] || { echo "[BOUNDARY] signature mismatch"; exit 3; }
else echo "[BOUNDARY] unsigned; create $s with $bs"; exit 4; fi
while IFS= read -r line; do
  [ -z "$line" ] && continue
  role=$(printf "%s" "$line" | cut -d" " -f1)
  path=$(printf "%s" "$line" | cut -d" " -f2-)
  case "$role" in
    PRIVATE) [ -e "$pack/$path" ] || { echo "[BOUNDARY] missing PRIVATE $path"; exit 5; } ;;
    PUBLIC)  [ -e "$pack/$path" ] || { echo "[BOUNDARY] missing PUBLIC $path"; exit 6; } ;;
    *) echo "[BOUNDARY] bad line: $line"; exit 7 ;;
  esac
done < "$b"
echo "[BOUNDARY] ok $pack"
