#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/minimal_tau.sh

safe_pair() {
  local out; out="$("$@" 2>/dev/null || true)"
  out="${out%$'\r'}"
  [ -z "$out" ] && out="0 0"
  # split to two fields
  set -- $out
  local s="${1:-0}" n="${2:-0}"
  printf '%s %s\n' "$s" "$n"
}

read -r s1 n1 <<<"$(safe_pair scripts/langlands/minimal_tau.sh dir_signature hecke .tau_ledger)"
n1=$((10#${n1})); [ "$n1" -gt 0 ] || n1=1
m1=$(( (10#${s1}) / n1 ))

read -r s2 n2 <<<"$(safe_pair scripts/langlands/hecke2_mean.sh .tau_ledger)"
n2=$((10#${n2})); [ "$n2" -gt 0 ] || n2=1
m2=$(( (10#${s2}) / n2 ))

printf 'A mean hecke=%d  hecke2=%d\n' "$m1" "$m2"
