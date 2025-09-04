#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LAKE="${HOME}/.elan/bin/lake.exe"
[[ -x "$LAKE" ]] || LAKE="lake"

sizes=(1 2 4 8 16 32)
tau="1.25"
qs="0,0.5,1,2"

now_ms() { date +%s%3N; }

"$LAKE" build >/dev/null
# warm-up
TC_WORK_REPS=1 "$LAKE" exe tau_crystal -- --tau "$tau" --q "$qs" --run-id warm --out /tmp/warm.json --audit true >/dev/null

echo "reps,time_ms,per_rep_ms"
for s in "${sizes[@]}"; do
  t0=$(now_ms)
  TC_WORK_REPS="$s" "$LAKE" exe tau_crystal -- --tau "$tau" --q "$qs" --run-id "r-$s" --out "/tmp/r_$s.json" --audit true >/dev/null
  t1=$(now_ms); dt=$((t1 - t0))
  pr=$(python - <<PY 2>/dev/null || echo $((dt / s))
dt=$dt; s=$s
print(int(round(dt/max(s,1))))
PY
)
  echo "$s,$dt,$pr"
done
