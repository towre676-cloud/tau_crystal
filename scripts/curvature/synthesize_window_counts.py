import json
from pathlib import Path
def L(p,d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
cover=L("artifacts/curvature/cover_windows.json",{"windows":[{"id":"U1"},{"id":"U2"},{"id":"U3"}]})
wins=[w.get("id") for w in (cover.get("windows") or []) if w.get("id")] or ["U1","U2","U3"]
raw=L("artifacts/echo/qcro_hist_raw.json",{"counts":{"sigma":1.0,"phi":1.0,"rho":1.0},"total":3.0})
base=raw.get("counts") or {"sigma":1.0,"phi":1.0,"rho":1.0}
if not isinstance(base,dict) or not base:\n  base={"sigma":1.0,"phi":1.0,"rho":1.0}
Path("artifacts/curvature/window_counts").mkdir(parents=True,exist_ok=True)
for uid in wins:\n  p=Path(f"artifacts/curvature/window_counts/{uid}.json")\n  if not p.exists() or p.stat().st_size==0:\n    p.write_text(json.dumps(base,separators=(",",":")))
print("ok")
