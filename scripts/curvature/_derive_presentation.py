import json
from pathlib import Path
g=json.loads(Path("artifacts/grammar/grammar.json").read_text())
P={"G":{"generators":list(dict.fromkeys(g.get("generators",[]))),"relations":g.get("relations",[])}, "ok":True}
Path("artifacts/curvature/G_presentation.json").write_text(json.dumps(P,separators=(",",":")))
