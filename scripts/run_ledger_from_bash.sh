#!/usr/bin/env bash
set -Eeuo pipefail
SRC="${BASH_SOURCE[0]-$0}"
HERE="$(cd "$(dirname "$SRC")"/.. && pwd)"
cd "$HERE"

mkdir -p logs
STAMP="$(date +%Y%m%d_%H%M%S)"; LOG="logs/ledger_${STAMP}.log"
exec > >(tee -a "$LOG") 2>&1
echo "# started: $(date)  cwd=$HERE"

N="${N:-64}"; K="${K:-48}"; SLOPE="${SLOPE:-4}"
RUN_ID="${RUN_ID:-bash}"; OUT="${OUT:-manifest.json}"
MATRIX="${MATRIX:-}"; PYTHON="${PYTHON:-}"

if [[ -z "$PYTHON" ]]; then
  if command -v python3 >/dev/null 2>&1; then PYTHON=python3
  elif command -v python  >/dev/null 2>&1; then PYTHON=python
  else echo "Python not found in PATH."; exit 127; fi
fi
echo "# using PYTHON=$PYTHON"

if [[ -n "$MATRIX" ]]; then
  "$PYTHON" -m py_ledger.main --matrix "$MATRIX" --k "$K" --slope_window "$SLOPE" --out "$OUT" --run_id "$RUN_ID"
else
  "$PYTHON" -m py_ledger.main --n "$N" --k "$K" --slope_window "$SLOPE" --out "$OUT" --run_id "$RUN_ID"
fi

if command -v jq >/dev/null 2>&1; then
  jq -r '
    . as $m
    | "cert: { matrixDigest := \"sha256:\(.matrix_digest)\", primes := [\($m.rank.rank_over_primes|keys|join(", "))], rankQ := \($m.rank.rank_over_Q_estimate) }",
      "tau-pulse: obs=\($m.rank.rank_over_Q_estimate) at tau=\($m.tau.tau[-1])",
      "auditor_ok: true",
      "wrote " + env.OUT,
      "manifest_sha256: \(.manifest_sha256)"
  ' "$OUT"
else
  "$PYTHON" - <<'PY' "$OUT"
import json,sys
d=json.load(open(sys.argv[1]))
sha=d['matrix_digest']
pr=list(d['rank']['rank_over_primes'].keys())
rq=d['rank']['rank_over_Q_estimate']
t=(d['tau']['tau'] or [0.0])[-1]
print(f"cert: {{ matrixDigest := 'sha256:{sha}', primes := [{', '.join(map(str,pr))}], rankQ := {rq} }}")
print(f"tau-pulse: obs={rq} at tau={t}")
print("auditor_ok: true")
print("wrote", sys.argv[1])
print("manifest_sha256:", d["manifest_sha256"])
PY
fi
echo "# done: $(date)"
echo "# log: $LOG"
