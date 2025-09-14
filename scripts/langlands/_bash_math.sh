#!/usr/bin/env bash
set -Eeuo pipefail; set +H
MICRO=1000000

# Convert decimal string in [0,1] to integer micro-units (base 10 only)
dec_to_micro(){
  v="${1:-0}"
  case "$v" in "" ) v="0";; .* ) v="0${v}";; esac
  A="${v%%.*}"; B="${v#*.}"
  [ "$v" = "$A" ] && B="0"
  # keep only digits; pad/truncate to 6
  B="${B%%[^0-9]*}"
  while [ "${#B}" -lt 6 ]; do B="${B}0"; done
  B="${B:0:6}"
  # force base-10 with 10# on both parts
  echo $(( 10#${A}*MICRO + 10#${B} ))
}

micro_clamp01(){
  x=$(( ${1:-0} )); if [ "$x" -lt 0 ]; then x=0; fi; if [ "$x" -gt $MICRO ]; then x=$MICRO; fi; echo "$x"
}

# Integer sqrt (Newton) on nonnegative integers
isqrt(){
  n=$(( ${1:-0} )); if [ "$n" -lt 2 ]; then echo "$n"; return; fi
  x=$n; y=$(( (x + 1) / 2 ))
  while [ "$y" -lt "$x" ]; do x=$y; y=$(( (x + n / x) / 2 )); done
  echo "$x"
}
