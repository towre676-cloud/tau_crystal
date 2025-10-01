#!/usr/bin/env python3
import json, os, glob, datetime
from pathlib import Path
def newest(p):
  c=[]
  for pat in p:
    for x in glob.glob(pat, recursive=True):
      try: c.append((os.path.getmtime(x), x))
      except FileNotFoundError: pass
  return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None
def main():
  ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
  out=Path(f"analysis/freed/twozero_placeholder_{ts}.json")
  defects=newest(["analysis/**/defect_6d_*.json",".tau_ledger/**/defect_6d_*.json"])
  payload={"angle":"twozero_placeholder","timestamp":ts,"status":"pending","inputs":{"defect_6d":defects},"note":"placeholder for (2,0) structures; will wire higher defect logic later"}
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
