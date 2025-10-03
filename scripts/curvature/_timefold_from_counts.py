import json,math
from pathlib import Path
cov=json.loads(Path("artifacts/curvature/cover_windows.json").read_text())
globalw=json.loads(Path("artifacts/echo/freq_hist_norm.json").read_text())["weights"]
prior=1.0; alph=("sigma","phi","rho")
out=[]
for w in cov.get("windows",[]):
  wid=w["id"]; p=Path(f"artifacts/curvature/window_counts/{wid}.json")
  if p.exists():
    c=json.loads(p.read_text())
    P=[float(c.get(a,0.0)) for a in alph]
  else:
    # fallback: use global weights as pseudo-counts
    P=[float(globalw[k]) for k in ("sigma","phi","rho")]
  Q=list(reversed(P))  # Theta: simple reversal as placeholder
  ps=sum(P)+prior*len(alph); qs=sum(Q)+prior*len(alph)
  kl=0.0
  for i,a in enumerate(alph):
    pa=(P[i]+prior)/ps; qa=(Q[i]+prior)/qs
    kl += pa*math.log(pa/qa)
  out.append({"window":wid,"kl":kl,"prior":prior})
Path("artifacts/curvature/timefold_kl.json").write_text(json.dumps({"timefold":out},separators=(",",":")))
