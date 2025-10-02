#!/usr/bin/env bash
# reflect_util.sh — tiny helper for τ‑Reflection artifacts (no jq)
set -euo pipefail
set +H
umask 022
export LC_ALL=C LANG=C

latest_json=""
latest_csv=""
for f in analysis/reflection/run_*/report.json; do
  [ -f "$f" ] || continue
  if [ -z "${latest_json-}" ] || [ "$f" -nt "$latest_json" ]; then latest_json="$f"; fi
done
for f in analysis/reflection/run_*/entropy.csv; do
  [ -f "$f" ] || continue
  if [ -z "${latest_csv-}" ] || [ "$f" -nt "$latest_csv" ]; then latest_csv="$f"; fi
done

_cmd="${1:-help}"

_strip_json() { tr -d '\r\n\t ' < "$latest_json"; }
_field_num()  { _strip_json | sed -n "s/.*\"$1\":\([0-9.]\+\).*/\1/p" | head -n1; }
_field_bool() { _strip_json | sed -n "s/.*\"$1\":\(\(true\|false\)\).*/\1/p" | head -n1; }

case "$_cmd" in
  path)
    [ -n "${latest_json-}" ] && echo "$latest_json" || { echo "no report.json found"; exit 66; }
    ;;
  rho)
    [ -n "${latest_json-}" ] || { echo "no report.json found"; exit 66; }
    _field_num spectral_radius
    ;;
  tail)
    N="${2:-3}"
    [ -n "${latest_csv-}" ] || { echo "no entropy.csv found"; exit 66; }
    awk -F, -v N="$N" 'NR>1{a[NR-1]=$3} END{n=NR-1;s=0;for(i=n;i>n-N&&i>=1;i--){x=a[i];if(x<0)x=-x;s+=x} printf "%.9f\n", s}' "$latest_csv"
    ;;
  tail-json)
    [ -n "${latest_json-}" ] || { echo "no report.json found"; exit 66; }
    _field_num tail_l1
    ;;
  eps)
    [ -n "${latest_json-}" ] || { echo "no report.json found"; exit 66; }
    _field_num tolerance
    ;;
  verdict)
    [ -n "${latest_json-}" ] || { echo false; exit 1; }
    _field_bool fixpoint || echo false
    ;;
  summary)
    [ -n "${latest_json-}" ] || { echo "[τ‑Reflection] no report.json found"; exit 66; }
    flat="$(_strip_json)"
    rho="$(printf "%s" "$flat" | sed -n 's/.*"spectral_radius":\([0-9.]\+\).*/\1/p' | head -n1)"
    tail="$(printf "%s" "$flat" | sed -n 's/.*"tail_l1":\([0-9.]\+\).*/\1/p' | head -n1)"
    eps="$(printf "%s" "$flat" | sed -n 's/.*"tolerance":\([0-9.]\+\).*/\1/p' | head -n1)"
    fix="$(printf "%s" "$flat" | sed -n 's/.*"fixpoint":\(\(true\|false\)\).*/\1/p' | head -n1)"
    echo "[τ‑Reflection] file=$latest_json  rho=$rho  tail=$tail  eps=$eps  fixpoint=$fix"
    ;;
  help|*)
    cat <<HLP
Usage: scripts/ci/reflect_util.sh <command> [args]
  path        -> print latest report.json path
  rho         -> print spectral radius (ρ)
  tail [N]    -> tail L1 from CSV (last N deltas, default 3)
  tail-json   -> tail L1 from report.json
  eps         -> epsilon/tolerance
  verdict     -> print 'true' or 'false' for fixpoint
  summary     -> human line with rho/tail/eps/verdict
HLP
    ;;
esac
