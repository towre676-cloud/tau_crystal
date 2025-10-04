import json
from pathlib import Path
p=Path("artifacts/seal/pushout_manifest.json")
d=json.loads(p.read_text())
d.setdefault("proof_cone_id","artifacts/proofs/cone_id_gf2.json")
d.setdefault("proof_cech","artifacts/proofs/cech_identities.json")
p.write_text(json.dumps(d,separators=(",",":")))
