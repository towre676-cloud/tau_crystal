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
  out=Path(f"analysis/freed/anomaly_inflow_{ts}.json")
  bulk=newest(["analysis/**/bulk_logdet_*.json",".tau_ledger/**/bulk_logdet_*.json"])
  bdry=newest(["analysis/**/eta_boundary_*.json",".tau_ledger/**/eta_boundary_*.json"])
  logB=newest(["analysis/**/logB_receipt_*.json",".tau_ledger/**/logB_receipt_*.json"])
  payload={
    "angle":"anomaly_inflow",
    "timestamp": ts,
    "status": "pending" if not (bulk and bdry and logB) else "ok",
    "bulk_logdet": bulk,
    "eta_boundary": bdry,
    "logB_receipt": logB,
    "diffK_class_ref": null,
    "note":"seed for Freed–Hopkins–Singer style inflow; will map (bulk+bdry)→diff K when class materializes"
  }
  out.parent.mkdir(parents=True, exist_ok=True)
  with open(out.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(out.with_suffix(".json.tmp"), out); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
