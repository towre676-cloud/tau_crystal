import json
from pathlib import Path
def L(p):
  try: return json.loads(Path(p).read_text())
  except: return None
out={"cone_id":L("artifacts/proofs/cone_id_gf2.json"),"cech":L("artifacts/proofs/cech_identities.json")}
print(json.dumps(out,separators=(",",":")))
