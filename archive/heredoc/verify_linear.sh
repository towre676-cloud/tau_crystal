#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LAKE="${HOME}/.elan/bin/lake.exe"
[[ -x "$LAKE" ]] || LAKE="lake"

# sizes = number of calls per measurement (total work ∝ size)
sizes=(1 2 4 8 16 32)
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

# build once
"$LAKE" build >/dev/null

# warm-up (amortize startup & JIT)
"$LAKE" exe tau_crystal -- --tau "$tau" --q "$qs" --run-id warmup --out /tmp/manifest_warm.json --audit true >/dev/null 2>&1 || true

echo "calls,total_ms,per_call_ms"
for s in "${sizes[@]}"; do
  t0=$(now_ms)
  for ((i=1;i<=s;i++)); do
    "$LAKE" exe tau_crystal -- --tau "$tau" --q "$qs" --run-id "scale-$s-$i" --out "/tmp/manifest_$s_$i.json" --audit true >/dev/null
  done
  t1=$(now_ms)
  dt=$((t1 - t0))
  avg=$(python - <<PY
dt=$dt; s=$s
print(int(round(dt/max(s,1))))
PY
)
  echo "$s,$dt,$avg"
done
