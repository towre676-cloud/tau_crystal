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
  out=Path(f"analysis/freed/renormalon_probe_{ts}.json")
  laurent=newest(["analysis/**/laurent_*drift*.json",".tau_ledger/**/laurent_*drift*.json"])
  taupulse=newest(["analysis/**/tau_pulse_*.json",".tau_ledger/**/tau_pulse_*.json"])
  payload={"angle":"renormalon_probe","timestamp":ts,"status":"pending","inputs":{"laurent_drift":laurent,"tau_pulses":taupulse},"note":"seed; later compare asymptotic slopes vs Borel proxies"}
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
