import json
from pathlib import Path
cj=json.loads(Path("artifacts/curvature/cocycle_cijk.json").read_text())
gens=set(json.loads(Path("artifacts/curvature/G_presentation.json").read_text())["G"]["generators"])
c=cj.get("cijk","id")
length = 0 if c=="id" else (1 if c in gens else 2)
Path("artifacts/curvature/length_metrics.json").write_text(json.dumps({"length":length,"c":c},separators=(",",":")))
