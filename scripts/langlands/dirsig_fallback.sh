#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
[ -f analysis/reciprocity_best.env ] && . analysis/reciprocity_best.env
if [ -n "${BEST_S_MICRO:-}" ] && [ -n "${BEST_T_MICRO:-}" ]; then
  printf "%s %s\n" "$BEST_S_MICRO" "$BEST_T_MICRO"; exit 0
fi
echo "0 0"
