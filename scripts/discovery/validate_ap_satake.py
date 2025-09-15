import json,sys
try:
  import jsonschema
except Exception:
  print("[warn] jsonschema not installed; skipping validation"); sys.exit(0)
sch=json.load(open("docs/schemas/ap_satake.schema.json",encoding="utf-8"))
for p in sys.argv[1:]:
  obj=json.load(open(p,encoding="utf-8"))
  jsonschema.validate(obj,sch); print("✓",p)
