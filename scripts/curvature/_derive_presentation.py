import json
from pathlib import Path
g=json.loads(Path("artifacts/grammar/grammar.json").read_text())
P={"G":g,"ok":True}
Path("artifacts/curvature/G_presentation.json").write_text(json.dumps(P,separators=(",",":")))
