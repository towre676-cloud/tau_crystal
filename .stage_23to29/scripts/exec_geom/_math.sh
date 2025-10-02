#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
gcd(){ a=${1:-0}; b=${2:-0}; a=${a#-}; b=${b#-}; while [ "$b" -ne 0 ]; do t=$((a%%b)); a=$b; b=$t; done; echo "${a:-0}"; }
lcm2(){ x=${1:-0}; y=${2:-0}; [ "$x" -eq 0 ] && echo 0 && return; g=$(gcd "$x" "$y"); echo $(( x / g * y )); }
lcm_list(){ L=1; while IFS= read -r a; do [ -z "$a" ] && continue; L=$(lcm2 "$L" "$a"); done; echo "$L"; }
