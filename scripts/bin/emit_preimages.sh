#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:-}"
CONTRACT="${2:?path/to/contract.json}"
REQUEST="${3:?path/to/request.json}"
stem(){ b="${1##*/}"; echo "${b%.receipt.json}"; }
base="${REC:+$(stem "$REC")}"
[ -n "${base:-}" ] || base="$(basename "$CONTRACT" .json)"
out_c="analysis/${base}.input.canon.ascii.json"
out_r="analysis/${base}.request.canon.json"
python3 - "$CONTRACT" > "$out_c" <<PY
import sys,json,pathlib
p=pathlib.Path(sys.argv[1])
with p.open("rb") as f: obj=json.load(f)
s=json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=True)
sys.stdout.write(s)
PY
python3 - "$REQUEST" > "$out_r" <<PY
import sys,json,pathlib
p=pathlib.Path(sys.argv[1])
with p.open("rb") as f: obj=json.load(f)
s=json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False)
sys.stdout.write(s)
PY
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
HC="$(sha "$out_c")"; HR="$(sha "$out_r")"
printf "wrote  %s  (sha256=%s)\n" "$out_c" "$HC"
printf "wrote  %s  (sha256=%s)\n" "$out_r" "$HR"
if [ -n "$REC" ] && [ -f "$REC" ]; then
  if command -v jq >/dev/null 2>&1; then
    IN_SHA="$(jq -r ".input_sha256" "$REC")"; REQ_SHA="$(jq -r ".request_sha256" "$REC")"
  else
    IN_SHA="$(grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
    REQ_SHA="$(grep -o "\"request_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
  fi
  echo "receipt.input_sha256 = $IN_SHA";   echo "preimage.contract = $HC"
  echo "receipt.request_sha256 = $REQ_SHA"; echo "preimage.request  = $HR"
  [ "$HC" = "$IN_SHA" ]  && echo "[OK] contract preimage matches"  || echo "[FAIL] contract preimage mismatch"
  [ "$HR" = "$REQ_SHA" ] && echo "[OK] request preimage matches"   || echo "[FAIL] request preimage mismatch"
fi
