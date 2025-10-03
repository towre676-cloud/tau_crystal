import json
from pathlib import Path
def L(p,d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
def f(x):\n  try:\n    v=float(x)\n    return v if v>0 else 0.0\n  except Exception:\n    return 0.0
C=L("artifacts/echo/graded_scalar_from_hist.json",{"graded_scalar":0.0}).get("graded_scalar",0.0)
E=L("artifacts/curvature/timefold_kl.json",{"mean_kl":0.0}).get("mean_kl",0.0)
C=f(C); E=f(E); O=C*E
Path("artifacts/obs/obs_value.json").write_text(json.dumps({"CRO_scalar":C,"ENT_scalar":E,"Obs":O},separators=(",",":")))
print("ok")
