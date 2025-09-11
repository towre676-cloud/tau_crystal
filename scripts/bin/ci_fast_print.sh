#!/usr/bin/env bash
set -euo pipefail; set +H
found=0
for f in Makefile */Makefile; do
  [ -f "$f" ] || continue
  awk 'BEGIN{in=0}'                                   >> "$X"
printf %sn '/^[[:space:]]*ci-fast[[:space:]]*:/ {in=1; print "----- ci-fast @ " FILENAME " -----"; print; next}' >> "$X"
printf %sn 'in==1 && /^[^ \t#][^:]*:/ {in=0; print "----- end -----"; next}'                                >> "$X"
printf %sn 'in==1 { line=$0; gsub(/\t/,"\\\\t",line); print line; next }'                                  >> "$X"
printf %sn '{ }' "$f" && found=1
done
[ "$found" -eq 1 ] || echo "(no ci-fast targets found)"
