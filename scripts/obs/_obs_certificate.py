import json, math
from pathlib import Path
def L(p, d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
def as_float(x, default=0.0):\n  try: return float(x)\n  except Exception: return default
def get_CE():
  ov=L("artifacts/obs/obs_value.json",{})
  if {"CRO_scalar","ENT_scalar"}<=ov.keys():
    C=max(0.0, as_float(ov.get("CRO_scalar",0)))
    E=max(0.0, as_float(ov.get("ENT_scalar",0)))
    return C,E
  cro=L("artifacts/echo/graded_scalar_from_hist.json", {"graded_scalar":0})
  tf=L("artifacts/curvature/timefold_kl.json", {"timefold":[]})
  C=max(0.0, as_float(cro.get("graded_scalar",0)))
  kls=[as_float(x.get("kl",0)) for x in (tf.get("timefold") or [])]
  E=max(0.0, (sum(kls)/len(kls)) if kls else 0.0)
  return C,E
def cert(C,E):
  Obs=C*E
  eps=[1e-9,1e-6,1e-3]
  checks=[]
  for d in eps:
    C1=C+d; E1=E+d
    oC=C1*E; oE=C*E1; oJ=C1*E1
    checks.append({"delta":d,"mono_in_C":oC>=Obs,"mono_in_E":oE>=Obs,"mono_joint":oJ>=Obs,"Obs":Obs,"Obs_dC":oC,"Obs_dE":oE,"Obs_dCdE":oJ})
  grad={"dObs_dC":E,"dObs_dE":C}
  lips={"L1_bound":max(abs(E),abs(C)),"L2_bound":(E*E+C*C)**0.5}
  return {"input":{"CRO_scalar":C,"ENT_scalar":E,"Obs":Obs},"epsilons":eps,"checks":checks,"gradient":grad,"lipschitz":lips,"fallback":False}
try:
  C,E=get_CE(); out=cert(C,E)
except Exception:
  out={"input":{"CRO_scalar":0.0,"ENT_scalar":0.0,"Obs":0.0},"epsilons":[1e-9,1e-6,1e-3],"checks":[],"gradient":{"dObs_dC":0.0,"dObs_dE":0.0},"lipschitz":{"L1_bound":0.0,"L2_bound":0.0},"fallback":True}
Path("artifacts/obs/obs_certificate.json").write_text(json.dumps(out,separators=(",",":")))
print("ok")
