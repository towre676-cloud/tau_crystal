import json,math,sys
from pathlib import Path
cov=json.loads(Path("artifacts/curvature/cover_windows.json").read_text())
prior=1.0  # Laplace prior to avoid zeros
alphabet=["sigma","phi","rho"]
out=[]
for w in cov.get("windows",[]):
    # placeholder equal counts; wire real counts later
    p={a:1.0 for a in alphabet}; q={a:1.0 for a in alphabet}
    ps=sum(p.values())+prior*len(alphabet)
    qs=sum(q.values())+prior*len(alphabet)
    kl=0.0
    for a in alphabet:
        pa=(p[a]+prior)/ps
        qa=(q[a]+prior)/qs
        kl += pa*math.log(pa/qa)
    out.append({"window":w["id"],"kl":kl,"prior":prior,"alphabet":alphabet})
Path("artifacts/curvature/timefold_kl.json").write_text(json.dumps({"timefold":out},separators=(",",":")))
