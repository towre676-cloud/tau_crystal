#!/usr/bin/env bash
set -euo pipefail; set +H
k="${1:-}"; N="${2:-}"
if [ -z "${k:-}" ] || [ -z "${N:-}" ]; then echo "usage: $0 weight level"; exit 2; fi
case "$k" in (*[!0-9]*|"") echo "weight int required"; exit 2;; esac
case "$N" in (*[!0-9]*|"") echo "level int required"; exit 2;; esac
n="$N"; prod_num="$N"; prod_den=1; p=2
while [ $((p*p)) -le "$n" ]; do
  if [ $((n%p)) -eq 0 ]; then
    prod_num=$(( prod_num*(p+1) ))
    prod_den=$(( prod_den*p ))
    while [ $((n%p)) -eq 0 ]; do n=$((n/p)); done
  fi
  p=$((p+1))
done
if [ "$n" -gt 1 ]; then prod_num=$(( prod_num*(n+1) )); prod_den=$(( prod_den*n )); fi
# B = floor( (k/12) * N * prod_{p|N} (1+1/p) )
num=$(( k * prod_num ))
den=$(( 12 * prod_den ))
B=$(( num / den ))
if [ "$B" -lt 1 ]; then B=1; fi
echo "$B"
