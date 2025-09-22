#!/usr/bin/env bash
set -Eeuo pipefail; set +H
root="${1:-.tau_ledger}"
. scripts/langlands/_bash_math.sh
sum=0; cnt=0
while IFS= read -r -d "" f; do
  sz=$(wc -c < "$f" 2>/dev/null || echo 0); t=$((sz+1)); lg=0; while [ $t -gt 1 ]; do t=$((t/2)); lg=$((lg+1)); done
  sum=$((sum+lg)); cnt=$((cnt+1))
done < <(find "$root" -type f -name "*.json" -print0 2>/dev/null)
printf "%s\t%s\t%s\n" "$root" "$sum" "$cnt"
