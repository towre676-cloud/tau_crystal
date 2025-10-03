import json
from pathlib import Path
P=json.loads(Path("artifacts/curvature/G_presentation.json").read_text())
G=set(P["G"]["generators"]+["id"])
gl=json.loads(Path("artifacts/curvature/glue_gij.json").read_text())
bad=[x for x in gl["gij"] if x["g"] not in G]
Path("artifacts/curvature/G_validation.json").write_text(json.dumps({"ok":len(bad)==0,"bad":bad,"generators":sorted(G)},separators=(",",":")))
