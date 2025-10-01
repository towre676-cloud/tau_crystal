#!/usr/bin/env python3
import json, os, glob, datetime
from pathlib import Path
def newest(pats):
  c=[]
  for pat in pats:
    for p in glob.glob(pat, recursive=True):
      try: c.append((os.path.getmtime(p), p))
      except FileNotFoundError: pass
  return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None
def main():
  ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
  out=Path(f"analysis/freed/tmf_index_probe_{ts}.json")
  # Inputs we might leverage later:
  dlogB=newest(["analysis/**/tmf_level_*.json",".tau_ledger/**/tmf_level_*.json"])
  entropy576=newest(["analysis/**/*entropy*576*.json",".tau_ledger/**/*entropy*576*.json"])
  payload={
    "angle":"tmf_index_probe",
    "timestamp": ts,
    "status":"pending",
    "method":"seed",
    "q_moments": null,
    "periodicity_hints": {"24": null, "576": null},
    "inputs": {"tmf_levels": dlogB, "entropy576": entropy576},
    "note":"scaffold only; will fill from tmf_level_* and entropy deltas later"
  }
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
