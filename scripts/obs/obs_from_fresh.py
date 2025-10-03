import json
from pathlib import Path
def L(p,d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
C=L("artifacts/echo/graded_scalar_from_hist.json",{"graded_scalar":0.0}).get("graded_scalar",0.0)
E=L("artifacts/curvature/timefold_kl.json",{"mean_kl":0.0}).get("mean_kl",0.0)
C=float(C) if C is not None else 0.0; E=float(E) if E is not None else 0.0
Path("artifacts/obs/obs_value.json").write_text(json.dumps({"CRO_scalar":max(0.0,C),"ENT_scalar":max(0.0,E),"Obs":max(0.0,C)*max(0.0,E)},separators=(",",":")))
print("ok")
