import json,math
from pathlib import Path
bet=json.loads(Path("artifacts/echo/cone_homology_nontrivial.json").read_text())["betti"]
hpath=Path("artifacts/echo/freq_hist.json")
freq={"sigma":1.0,"phi":1.0,"rho":1.0}
if hpath.exists():
    try:
        raw=json.loads(hpath.read_text())
        f=raw.get("freq",{})
        for k in ("sigma","phi","rho"): freq[k]=float(f.get(k,freq[k]))
    except: pass
w=[freq["sigma"],freq["phi"],freq["rho"]]
wsum=sum(w) or 1.0
w=[x/wsum for x in w]
g=float(sum(bet))*float(sum(w))
out={"betti":bet,"weights":w,"graded_scalar":g}
Path("artifacts/echo/graded_scalar_from_hist.json").write_text(json.dumps(out,separators=(",",":")))
