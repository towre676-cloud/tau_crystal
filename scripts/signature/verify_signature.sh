#!/usr/bin/env bash
set -Eeuo pipefail; set +H
sigpath="${1:-latest}"
dir=".tau_ledger/signature"
if [ "$sigpath" = "latest" ]; then sigpath=$(ls -1 "$dir"/sigv1-*.sig 2>/dev/null | LC_ALL=C sort | tail -n 1); fi
[ -n "$sigpath" ] || { echo "::error ::no signature found"; exit 1; }
fail=0
while IFS= read -r rule; do
  case "$rule" in
    require:file:*) f=${rule#require:file:}; [ -f "$f" ] || { echo "::error ::missing file $f"; fail=1; } ;;
    require:dir:*)  d=${rule#require:dir:};  [ -d "$d" ] || { echo "::error ::missing dir $d";  fail=1; } ;;
    forbid:glob:*)  pat=${rule#forbid:glob:}; match=$(ls -1 -- $pat 2>/dev/null | head -n 1 || true); [ -z "$match" ] || { echo "::error ::forbidden match: $match"; fail=1; } ;;
    note:*) : ;;
    *) echo "::warning ::unknown rule: $rule" ;;
  esac
done < "$sigpath"
[ "$fail" -eq 0 ] && echo "OK: signature satisfied" || { echo "FAIL: signature violations"; exit 1; }
