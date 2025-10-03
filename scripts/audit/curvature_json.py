import json
from pathlib import Path
def L(p):
    try: return json.loads(Path(p).read_text())
    except: return None
out={
 "cover":L("artifacts/curvature/cover_windows.json"),
 "glue":L("artifacts/curvature/glue_gij.json"),
 "cocycle":L("artifacts/curvature/cocycle_cijk.json"),
 "length":L("artifacts/curvature/length_metrics.json"),
 "timefold":L("artifacts/curvature/timefold_kl.json")}
print(json.dumps(out,separators=(",",":")))
