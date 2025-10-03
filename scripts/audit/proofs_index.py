import json, os
from pathlib import Path
def load_json(p):
  try: return json.loads(Path(p).read_text())
  except Exception: return None
def exists(p): return Path(p).exists()
cone="artifacts/proofs/cone_id_gf2.json"
cech="artifacts/proofs/cech_identities.json"
leans=[
 "lean/Core/ConeIdAcyclic.lean",
 "lean/Core/ConeAcyclicSmall.lean",
 "lean/Core/CechIdentities.lean",
 "lean/Core/CechProofMinimal.lean"]
out={
 "cone_id_witness": cone,
 "cech_witness": cech,
 "cone_exists": exists(cone),
 "cech_exists": exists(cech),
 "lean_files": [{"path":p,"exists":exists(p)} for p in leans],
 "cone_payload": load_json(cone),
 "cech_payload": load_json(cech)
}
Path("artifacts/audit/proofs_index.json").write_text(json.dumps(out,separators=(",",":")))
