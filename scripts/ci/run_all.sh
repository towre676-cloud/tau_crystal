#!/usr/bin/env bash
set +e; set +o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
mkdir -p ops/ci_logs
echo "[run-all] sanitizing canon JSONs…"
bash scripts/ci/_sanitize_canons.sh > ops/ci_logs/_sanitize.out 2> ops/ci_logs/_sanitize.err || true
scripts=(
  "scripts/ci/check_anomaly_glue.sh"
  "scripts/ci/check_modular.sh"
  "scripts/ci/check_specnet.sh"
  "scripts/ci/check_chamber.sh"
  "scripts/ci/check_padic.sh"
  "scripts/ci/check_sset.sh"
)
fail=0
for s in "${scripts[@]}"; do
  name=$(basename "$s"); out="ops/ci_logs/${name%.sh}.out"; err="ops/ci_logs/${name%.sh}.err"
  echo "[run-all] >>> $s"
  bash "$s" >"$out" 2>"$err"
  rc=$?
  if [ "$rc" -eq 0 ]; then echo "[run-all] OK  ($s)";
  else echo "[run-all] FAIL($rc) $s — tailing logs"; tail -n 40 "$out" || true; tail -n 40 "$err" || true; fail=1; fi
done
echo "[run-all] logs -> ops/ci_logs/"; exit "$fail"
