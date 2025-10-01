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
  out=Path(f"analysis/freed/wkb_opers_scout_{ts}.json")
  entropy=newest(["analysis/**/entropy_pulse_*.json",".tau_ledger/**/entropy_pulse_*.json"])
  cheb=newest(["analysis/**/chebyshev_*decay*.json",".tau_ledger/**/chebyshev_*decay*.json"])
  payload={"angle":"wkb_opers_scout","timestamp":ts,"status":"pending","inputs":{"entropy_pulse":entropy,"chebyshev_decay":cheb},"note":"scout only; next step extracts Stokes/turning data"}
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
