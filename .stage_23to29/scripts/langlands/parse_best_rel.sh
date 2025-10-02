#!/usr/bin/env bash
set -Eeuo pipefail; set +H
F="${1:-analysis/bash_theta_scan.tsv}"
TOL="${2:-1000}"
[ -f "$F" ] || { echo "[err] not found: $F" >&2; exit 2; }
best_abs=999999999; best_abs_line=""
best_rel_ppm=999999999; best_rel_line=""
exec 9<"$F"; IFS= read -r _hdr <&9 || true
while IFS= read -r line <&9; do
  [ -z "${line:-}" ] && continue
  first="${line%%[ 	]*}"; case "$first" in S_micro*|"#"*) continue;; esac
  set -- $line
  S="${1:-}"; T="${2:-}"; D="${3:-}"; mA="${4:-}"
  [ -z "$S" ] || [ -z "$D" ] && continue
  D=$(( D + 0 )); mA=$(( mA + 0 ))
  # absolute min
  if [ "$D" -lt "$best_abs" ]; then best_abs="$D"; best_abs_line="$line"; fi
  # relative ppm = floor(1e6 * D / (1+mA))
  den=$(( 1 + mA ))
  rel_ppm=$(( (1000000 * D) / den ))
  if [ "$rel_ppm" -lt "$best_rel_ppm" ]; then best_rel_ppm="$rel_ppm"; best_rel_line="$line"; fi
done; exec 9<&-
echo "ABS best_diff_micro=$best_abs | $best_abs_line"
echo "REL best_diff_ppm=$best_rel_ppm | $best_rel_line"
if [ "$best_abs" -le "$TOL" ]; then echo "[ok] reciprocity within tol"; exit 0; fi
echo "[fail] reciprocity outside tol"; exit 1
