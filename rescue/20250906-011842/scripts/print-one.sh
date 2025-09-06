#!/usr/bin/env bash
set -u
first="$(ls -1 manifests/*.json 2>/dev/null | head -n 1 || true)"
[ -z "$first" ] && { echo "[print-one] no manifests"; exit 0; }
python - <<'PY'
import json,glob,sys
files=sorted(glob.glob("manifests/*.json"))
if not files: sys.exit(0)
with open(files[0],"r",encoding="utf-8") as f:
    doc=json.load(f)
print(json.dumps(doc,indent=2,ensure_ascii=False))
PY
