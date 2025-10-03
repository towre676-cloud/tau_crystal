import json
from pathlib import Path
bet=json.loads(Path("artifacts/echo/cone_homology_nontrivial.json").read_text())["betti"]
w=json.loads(Path("artifacts/echo/freq_hist_norm.json").read_text())["weights"]
weights=[w["sigma"],w["phi"],w["rho"]]
g=float(sum(bet))*float(sum(weights))
Path("artifacts/echo/graded_scalar_from_hist.json").write_text(json.dumps({"betti":bet,"weights":weights,"graded_scalar":g},separators=(",",":")))
