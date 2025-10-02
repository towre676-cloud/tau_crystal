#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

# powmod and Legendre
powmod(){ local a="$1" e="$2" p="$3" r=1; a=$((a%p)); [ "$a" -lt 0 ] && a=$((a+p))
  while [ "$e" -gt 0 ]; do
    if [ $((e&1)) -eq 1 ]; then r=$(( (r*a)%p )); fi
    a=$(( (a*a)%p )); e=$((e>>1))
  done
  printf '%d\n' "$r"
}
legendre(){ # (a|p)
  local a="$1" p="$2"
  [ $((a%p)) -eq 0 ] && { echo 0; return; }
  # Euler's criterion: a^((p-1)/2) ≡ ±1 (mod p)
  local t; t=$(powmod "$a" $(((p-1)/2)) "$p")
  [ "$t" -eq 1 ] && echo 1 || echo -1
}

# Hasse ratio diagnostic |a_p|^2/(4p) as integer arithmetic (rounded down)
hasse_ratio_q16(){ # ap p -> floor( 2^16 * ap^2/(4p) )
  local ap="$1" p="$2"
  local num=$(( ap*ap << 14 ))   # (ap^2) * 2^14 (since /4 = <<(-2))
  printf '%d\n' $(( num / p ))
}

# simple dual-scale “stability” for L(1/2): two cutoffs, same printed decimal
stable_decimal_12(){ # v1 v2 -> prints "1" if formatted to 12dps equal
  local v1="$1" v2="$2"
  local s1 s2
  s1=$(awk -v x="$v1" 'BEGIN{printf "%.12f", x}')
  s2=$(awk -v x="$v2" 'BEGIN{printf "%.12f", x}')
  [ "$s1" = "$s2" ] && echo 1 || echo 0
}
