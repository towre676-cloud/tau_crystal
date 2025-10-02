#!/usr/bin/env bash
set -E -o pipefail; set +H
op="$1"; shift || true

# Try the native helper first
try="$(scripts/langlands/minimal_tau.sh dir_signature "$op" "$@" 2>/dev/null || true)"
try="$(printf '%s\n' "$try" | tr -d '\r' | tr '\t' ' ' )"

# Extract first two strict integers without grep -Eo (Git Bash compat)
pair="$(printf '%s' "$try" | awk '
  {
    n=split($0,w,/[^0-9-]+/); c=0;
    for(i=1;i<=n;i++){
      if (w[i] ~ /^-?[0-9]+$/) { printf("%s%s",(c++?" ":""),w[i]); if(c==2)break; }
    }
  }')"
set -- $pair
a="${1:-}"; b="${2:-}"

if [ -n "$a" ] && [ -n "$b" ] && [ "$a" != 0 -o "$b" != 0 ]; then
  printf '%s %s\n' "$a" "$b"; exit 0
fi

# Fallback (robust)
exec scripts/langlands/dirsig_fallback.sh "$op" "$@"
