#!/usr/bin/env bash
set -euo pipefail
A="${1:?first manifest}"; B="${2:?second manifest}"
if command -v jq >/dev/null 2>&1; then
  jq -S . "$A" > "$A.sorted.json"
  jq -S . "$B" > "$B.sorted.json"
  diff -u "$A.sorted.json" "$B.sorted.json" || true
  rm -f "$A.sorted.json" "$B.sorted.json"
else
  python - <<'PY' "$A" "$B"
import json, sys
a=json.load(open(sys.argv[1])); b=json.load(open(sys.argv[2]))
def flat(d,prefix=""):
  out={}
  if isinstance(d,dict):
    for k,v in d.items():
      out.update(flat(v,prefix+str(k)+"."))
  elif isinstance(d,list):
    for i,v in enumerate(d):
      out.update(flat(v,prefix+str(i)+"."))
  else:
    out[prefix[:-1]]=d
  return out
fa,fb=flat(a),flat(b)
keys=sorted(set(fa)|set(fb))
for k in keys:
  va=fa.get(k,"<missing>"); vb=fb.get(k,"<missing>")
  if va!=vb:
    print(f"- {k}: {va}\n+ {k}: {vb}\n")
PY
fi
