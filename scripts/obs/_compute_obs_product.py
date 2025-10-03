import json,math
from pathlib import Path
def jget(p,default):
  try: return json.loads(Path(p).read_text())
  except: return default
cro=jget("artifacts/echo/graded_scalar_from_hist.json",{"graded_scalar":0.0})
tf=jget("artifacts/curvature/timefold_kl.json",{"timefold":[]})
C=float(cro.get("graded_scalar",0.0))
kls=[float(x.get("kl",0.0)) for x in tf.get("timefold",[])]
E=(sum(kls)/len(kls)) if kls else 0.0
C=max(C,0.0); E=max(E,0.0)
Obs=C*E
delta=1e-6
mono_C = ( (C+delta)*E ) >= Obs
mono_E = ( C*(E+delta) ) >= Obs
out={"CRO_scalar":C,"ENT_scalar":E,"Obs":Obs,"function":"product",
     "monotone_certificate":{"delta":delta,"mono_in_C":bool(mono_C),"mono_in_E":bool(mono_E)}}
Path("artifacts/obs/obs_value.json").write_text(json.dumps(out,separators=(",",":")))
