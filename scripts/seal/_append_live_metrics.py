import json
from pathlib import Path
p=Path("artifacts/seal/pushout_manifest.json")
d=json.loads(p.read_text())
d["echo_nontrivial"]="artifacts/echo/graded_scalar_from_hist.json"
d["timefold"]="artifacts/curvature/timefold_kl.json"
p.write_text(json.dumps(d,separators=(",",":")))
