#!/usr/bin/env bash
set -euo pipefail
ROOT="${ROOT:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

# pick a Python
PYBIN="${PYBIN:-}"
if [ -z "${PYBIN}" ]; then
  if command -v python3 >/dev/null 2>&1; then PYBIN=python3
  elif command -v python  >/dev/null 2>&1; then PYBIN=python
  elif command -v py      >/dev/null 2>&1; then PYBIN="py -3"
  else echo "[err] python not found"; exit 1
  fi
fi

OUT=".tau_ledger/soliton_envelope.json"
K="${K:-1.0}"
DELTA="${DELTA:-0.0}"
N="${N:-2048}"
XMIN="${XMIN:- -20.0}"
XMAX="${XMAX:-  20.0}"
EXPECT="${EXPECT:-}"

CMD=( $PYBIN tools/soliton_envelope.py --k "$K" --delta "$DELTA" --n "$N" --xmin "$XMIN" --xmax "$XMAX" --out "$OUT" )
[ -n "$EXPECT" ] && CMD+=( --expect "$EXPECT" )

echo "[run] ${CMD[*]}" >&2
JSON="$("${CMD[@]}")"   # also prints to stdout, we capture for grep
echo "$JSON" | sed -E 's/,"u_max":[^,]+,/,/; s/,"l2":[^}]+}/}/' >/dev/null 2>&1 || true

# extract sha (jq if present; else grep)
if command -v jq >/dev/null 2>&1; then
  SHA=$(jq -r '.sha256' <<<"$JSON")
else
  SHA=$(printf "%s" "$JSON" | grep -oE '"sha256":"[0-9a-fA-F]+"' | head -n1 | sed -E 's/.*:"([0-9a-fA-F]+)".*/\1/')
fi

[ -n "$SHA" ] || { echo "[err] could not find sha256 in output"; exit 1; }
echo "[OK] soliton_envelope.sha256 = $SHA"
echo "$SHA" > .tau_ledger/SOLITON_SHA256
exit 0
