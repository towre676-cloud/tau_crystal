#!/usr/bin/env bash
set -u
shopt -s nullglob

ok=0; bad=0
files=(manifests/*.json)

for f in "${files[@]}"; do
  py=$(
    F="$f" python - <<'PY'
import os, json, hashlib
p=os.environ['F']
with open(p, 'r', encoding='utf-8') as fh:
    doc = json.load(fh)
core = dict(doc); core.pop('attest', None)
h = hashlib.sha256(json.dumps(core, separators=(',',':'), sort_keys=True).encode()).hexdigest()
print(h)
PY
  )
  base="${f##*/}"; base="${base%.json}"
  if [ "$py" = "$base" ]; then
    ok=$((ok+1))
  else
    echo "[hash mismatch] $f"
    bad=$((bad+1))
  fi
done

total=$((ok+bad))
echo "[verify] manifests = $total"
if [ "$bad" -eq 0 ]; then
  echo "[verify] OK ($ok files)"
  exit 0
else
  echo "[verify] FAIL ($bad bad)"
  exit 1
fi
