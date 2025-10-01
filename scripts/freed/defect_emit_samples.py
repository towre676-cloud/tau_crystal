#!/usr/bin/env python3
import json,datetime; from pathlib import Path
ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
paths=[Path(f"analysis/freed/defect_{i}_{ts}.json") for i in (1,2,3)]
for i,p in enumerate(paths,1):
  p.parent.mkdir(parents=True,exist_ok=True)
  a,b,c = ("α","β","γ") if i!=3 else ("β","γ","δ")
  with open(p.with_suffix(".json.tmp"),"w",encoding="utf-8") as f:
    json.dump({"a":a,"b":b,"c":c,"note":"sample defect fusion triple"},f,indent=2)
  p.with_suffix(".json.tmp").replace(p)
print(paths[0].as_posix())
