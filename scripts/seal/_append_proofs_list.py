import json
from pathlib import Path
p=Path("artifacts/seal/pushout_manifest.json")
d=json.loads(p.read_text())
d.setdefault("proofs",["lean/Core/ConeIdAcyclic.lean","lean/Core/ConeAcyclicSmall.lean","lean/Core/CechIdentities.lean","lean/Core/CechProofMinimal.lean"])
p.write_text(json.dumps(d,separators=(",",":")))
