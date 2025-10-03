import json
from pathlib import Path
p=Path("artifacts/seal/pushout_manifest.json")
d=json.loads(p.read_text())
d["subcat_D"]="artifacts/seal/subcat_D.json"
d["delta_N"]="artifacts/seal/delta_N.json"
p.write_text(json.dumps(d,separators=(",",":")))
