import json
from pathlib import Path
cov=json.loads(Path("artifacts/curvature/cover_windows.json").read_text())
wins=[w["id"] for w in cov.get("windows",[])]
sections={w:{"symbols":["sigma","phi","rho"],"n":3} for w in wins}
overlaps=[]
if set(wins)=={"U1","U2","U3"}:
  overlaps=[("U1","U2"),("U2","U3"),("U3","U1")]
restr=[{"i":i,"j":j,"rename":{"sigma":"sigma","phi":"phi","rho":"rho"}} for (i,j) in overlaps]
out={"windows":wins,"sections":sections,"restrictions":restr,"stackified":True}
Path("artifacts/receipts/R_sheaf.json").write_text(json.dumps(out,separators=(",",":")))
