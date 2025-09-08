#!/usr/bin/env bash
set -euo pipefail
ROOT="${ROOT:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

# choose python
PYBIN="${PYBIN:-}"
if [ -z "${PYBIN}" ]; then
  if command -v python3 >/dev/null 2>&1; then PYBIN=python3
  elif command -v python  >/dev/null 2>&1; then PYBIN=python
  elif command -v py      >/dev/null 2>&1; then PYBIN="py -3"
  else echo "[err] python not found"; exit 1
  fi
fi

mkdir -p .tau_ledger media
JSON_OUT=".tau_ledger/tau_tanh_2soliton.json"
PGM_OUT="media/tau_tanh_demo.pgm"
PNG_OUT="media/tau_tanh_demo.png"

K1="${K1:-1.0}"
K2="${K2:-0.7}"
D1="${D1:- -4.0}"
D2="${D2:-  3.0}"
N="${N:-2048}"
XMIN="${XMIN:- -20.0}"
XMAX="${XMAX:-  20.0}"
EXPECT="${EXPECT:-}"

CMD=( $PYBIN examples/tau_tanh_demo.py --k1 "$K1" --k2 "$K2" --d1 "$D1" --d2 "$D2" --n "$N" --xmin "$XMIN" --xmax "$XMAX" --out "$JSON_OUT" --pgm "$PGM_OUT" )
[ -n "$EXPECT" ] && CMD+=( --expect "$EXPECT" )

echo "[run] ${CMD[*]}" >&2
JSON="$("${CMD[@]}")"   # capture stdout for hash

# parse hash
if command -v jq >/dev/null 2>&1; then
  SHA=$(jq -r '.sha256' <<<"$JSON")
else
  SHA=$(printf "%s" "$JSON" | grep -oE '"sha256":"[0-9a-fA-F]+"' | head -n1 | sed -E 's/.*:"([0-9a-fA-F]+)".*/\1/')
fi
[ -n "$SHA" ] || { echo "[err] could not parse sha256"; exit 1; }

# optional PGM -> PNG conversion
if command -v magick >/dev/null 2>&1; then
  magick "$PGM_OUT" "$PNG_OUT" && echo "[img] wrote $PNG_OUT"
elif command -v convert >/dev/null 2>&1; then
  convert "$PGM_OUT" "$PNG_OUT" && echo "[img] wrote $PNG_OUT"
else
  echo "[img] wrote $PGM_OUT (no ImageMagick; PNG skipped)"
fi

echo "$SHA" > .tau_ledger/TAU_TANH2_SHA256
echo "[OK] tau_tanh_2soliton.sha256 = $SHA"
exit 0
