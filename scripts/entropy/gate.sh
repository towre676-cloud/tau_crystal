#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
CMP="${1:-}"; [ -n "$CMP" ] || { echo "[err] usage: gate.sh compare.json"; exit 64; }
[ -f "$CMP" ] || { echo "[err] not found: $CMP"; exit 66; }
LIM="${GZIP_RATIO_LIMIT:-0.02}"
J="$(tr -d "\r\n" < "$CMP")"
TDELTA="$(printf "%s" "$J" | sed -n 's/.*"summary":{[^}]*"total_size_delta":\([-0-9][0-9]*\).*/\1/p')"
[ -n "${TDELTA:-}" ] || { echo "[err] could not parse total_size_delta"; exit 65; }
fail=0
if [ "$TDELTA" -gt 0 ]; then echo "[gate] FAIL: total_size_delta=$TDELTA > 0"; fail=1; else echo "[gate] OK: total_size_delta=$TDELTA"; fi
rest="$(printf "%s" "$J" | sed -n 's/.*"entries":\[\(.*\)\],"summary".*/\1/p')"
viol=0; maxv=0
while [[ "$rest" =~ \"gzip_ratio\":\{[^}]*\"delta\":([0-9\.\-]+)\} ]]; do
  v="${BASH_REMATCH[1]}"; rest="${rest#*\"delta\":$v}";
  # compare v > LIM using awk for floats
  gt="$(awk -v x="$v" -v y="$LIM" "BEGIN{print (x>y)?1:0}")"
  if [ "$gt" = "1" ]; then viol=$((viol+1)); fi
  mv="$(awk -v a="$maxv" -v b="$v" "BEGIN{print (b>a)?b:a}")"; maxv="$mv"
done
if [ "$viol" -gt 0 ]; then echo "[gate] FAIL: gzip_ratio.delta violations=$viol (max=$maxv, limit=$LIM)"; fail=1; else echo "[gate] OK: gzip_ratio.delta <= $LIM (max=$maxv)"; fi
exit "$fail"
