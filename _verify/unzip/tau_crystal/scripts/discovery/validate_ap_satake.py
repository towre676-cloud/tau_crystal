import json,sys,os
try:
  import jsonschema
except Exception:
  print("[warn] jsonschema not installed; skipping validation")
  sys.exit(0)
sch=json.load(open("docs/schemas/ap_satake.schema.json",encoding="utf-8"))
def canon(p):
  s=open(p,encoding="utf-8",errors="replace").read(); i=s.find("{")
  if i<0: raise SystemExit(f"[err] no object in {p}")
  obj,_=json.JSONDecoder().raw_decode(s[i:])
  open(p,"w",encoding="utf-8").write(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n")
for p in sys.argv[1:]:
  canon(p)
  obj=json.load(open(p,encoding="utf-8"))
  jsonschema.validate(obj,sch)
  print("[ok]", os.path.basename(p))
