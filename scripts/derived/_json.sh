#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
out="${1:?}"; shift; : > "$out"; printf "{" > "$out"; first=1
while [ "$#" -gt 0 ]; do k="$1"; v="$2"; shift 2;
  [ $first -eq 1 ] || printf "," >> "$out"; first=0
  printf "\"%s\":" "$k" >> "$out"
  case "$v" in __RAW__*) printf "%s" "${v#__RAW__}" >> "$out" ;; *) printf "\"%s\"" "$v" >> "$out" ;; esac
done; printf "\n}\n" >> "$out"
