#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

g0="${1:-0.1}"; ell="${2:-0.25}"; b="${3:-0.5}"; b1="${4:-0.1}"
OUT_DIR=".tau_ledger/rgflow"; mkdir -p "$OUT_DIR"

TS="$(date -u +%Y%m%dT%H%M%SZ)"
JSON="$(scripts/flow/two_loop_solver.py "$g0" "$ell" "$b" "$b1")"
echo "$TS" > "$OUT_DIR/ts.txt"

REC="$OUT_DIR/receipt.tsv"
if [ ! -f "$REC" ]; then printf "mode\tparams\toutput\n" > "$REC"; fi

params_one=$(printf "mu0=1.0,g0=%.2f,ell=%.2f,b=%.2f" "$g0" "$ell" "$b")
params_two=$(printf "mu0=1.0,g0=%.2f,ell=%.2f,b=%.2f,b1=%.2f" "$g0" "$ell" "$b" "$b1")

one_json=$(python3 - <<'PY' "$JSON"
import json,sys
j=json.loads(sys.argv[1])
print(json.dumps({"mode":"one","mu0":1.0,"g0":j["g0"],"ell":j["ell"],"b":j["b"], **j.get("one",{})}, separators=(',',':')))
PY
)

two_json=$(python3 - <<'PY' "$JSON"
import json,sys
j=json.loads(sys.argv[1])
d={"mode":"two","mu0":1.0,"g0":j["g0"],"ell":j["ell"],"b":j["b"],"b1":j["b1"]}
d.update(j.get("two",{}))
print(json.dumps(d, separators=(',',':')))
PY
)

printf "one\t%s\t%s\n" "$params_one" "$one_json" >> "$REC"
printf "two\t%s\t%s\n" "$params_two" "$two_json" >> "$REC"

write_sha () {
  local f="$1" out="$2"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$f" | awk '{print $1}' > "$out"
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$f" | awk '{print $1}' > "$out"
  elif command -v python3 >/dev/null 2>&1; then
    python3 - "$f" > "$out" <<'PY'
import hashlib, sys, pathlib
p = pathlib.Path(sys.argv[1]); print(hashlib.sha256(p.read_bytes()).hexdigest())
PY
  else
    : > "$out"
  fi
}

# Hash the receipt BEFORE appending the SHA row, then append a row that records it
TMP="$OUT_DIR/.receipt.tmp"
cp "$REC" "$TMP"
write_sha "$TMP" "$OUT_DIR/receipt.sha256" || true
rm -f "$TMP"
printf "SHA256\t%s\n" "$(cat "$OUT_DIR/receipt.sha256" 2>/dev/null || printf '')" >> "$REC"
