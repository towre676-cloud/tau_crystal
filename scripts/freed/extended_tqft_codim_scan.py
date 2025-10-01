#!/usr/bin/env python3
import json, glob, os, datetime
from pathlib import Path
def have(pats):
  for pat in pats:
    if glob.glob(pat, recursive=True): return True
  return False
def main():
  ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
  out=Path(f"analysis/freed/extended_tqft_codim_{ts}.json")
  codim={
    "0D": have(["analysis/**/point_*.json",".tau_ledger/**/point_*.json"]),
    "1D": have(["analysis/**/line_*.json",".tau_ledger/**/line_*.json"]),
    "2D": have(["analysis/**/surface_*.json",".tau_ledger/**/surface_*.json"]),
    "3D": have(["analysis/**/bulk_*.json",".tau_ledger/**/bulk_*.json"]),
  }
  payload={"angle":"extended_tqft_codim_scan","timestamp":ts,"status":"ok","codimension":codim,"note":"presence-only scan; deep structure pending"}
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
