#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LAKE="${HOME}/.elan/bin/lake.exe"
[[ -x "$LAKE" ]] || LAKE="lake"

sizes=(1 2 4 8)   # adjust to your generator
tau="1.25"
qs="0,0.5,1,2"

now_ms() {
  if command -v python >/dev/null 2>&1; then
    python - <<'PY'
import time; print(int(time.time()*1000))
PY
  else
    date +%s%3N
  fi
}

echo "size,nnz,time_ms"
for s in "${sizes[@]}"; do
  t0=$(now_ms)
  "$LAKE" exe tau_crystal -- --tau "$tau" --q "$qs" --run-id "scale-$s" --out "manifest_scale_$s.json" --audit true >/dev/null
  t1=$(now_ms)
  dt=$((t1 - t0))
  echo "$s,$s,$dt"
done
