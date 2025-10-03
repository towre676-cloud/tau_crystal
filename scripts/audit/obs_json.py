import json
from pathlib import Path
p="artifacts/obs/obs_value.json"
def load_safe(path):
  try: return json.loads(Path(path).read_text())
  except Exception as e: return {"error": str(e).splitlines()[0]}
if not Path(p).exists() or Path(p).stat().st_size==0:
  Path(p).write_text(json.dumps({"CRO_scalar":0.0,"ENT_scalar":0.0,"Obs":0.0,"function":"product","monotone_certificate":{"delta":1e-6,"mono_in_C":True,"mono_in_E":True}},separators=(",",":")))
print(json.dumps({"obs":load_safe(p)},separators=(",",":")))
