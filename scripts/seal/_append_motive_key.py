import json
from pathlib import Path
p=Path("artifacts/seal/pushout_manifest.json")
d=json.loads(p.read_text())
d.setdefault("motive","artifacts/motive/period_values.json")
p.write_text(json.dumps(d,separators=(",",":")))
