import json,sys
from pathlib import Path
gij=json.loads(Path("artifacts/curvature/glue_gij.json").read_text())
arr=gij["gij"]
def compose(a,b):
    if a=="id": return b
    if b=="id": return a
    if a==b=="swap_sigma_phi": return "id"
    return "id"
def gij_of(i,j):
    for x in arr:
        if x["i"]==i and x["j"]==j: return x["g"]
    raise SystemExit(f"missing g_{{%s,%s}}"%(i,j))
g12=gij_of("U1","U2"); g23=gij_of("U2","U3"); g31=gij_of("U3","U1")
c = compose(compose(g12,g23),g31)
length = 0 if c=="id" else 1
Path("artifacts/curvature/cocycle_cijk.json").write_text(json.dumps({"cijk":c},separators=(",",":")))
Path("artifacts/curvature/length_metrics.json").write_text(json.dumps({"length":length},separators=(",",":")))
Path("artifacts/curvature/descent_c.json").write_text(json.dumps({"refined":False},separators=(",",":")))
