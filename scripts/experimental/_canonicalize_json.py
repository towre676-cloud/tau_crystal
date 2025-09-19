#!/usr/bin/env python3
import io, json, os, sys
p=sys.argv[1] if len(sys.argv)>1 else None
assert p and os.path.isfile(p), f"[canonicalize] missing file: {p}"
with open(p,"rb") as f: data=f.read()
try:
  obj=json.loads(data)
except json.JSONDecodeError as e:
  sys.stderr.write(f"[truncation] %s: %s\\n"%(p,str(e))); sys.exit(3)
if not isinstance(obj, dict):
  sys.stderr.write(f"[schema] top-level is not object: {p}\\n"); sys.exit(4)
txt=json.dumps(obj, sort_keys=True, separators=(",",":")) + "\n"
tmp=p+".tmp"; open(tmp,"w",encoding="utf-8", newline="\n").write(txt); os.replace(tmp,p)
