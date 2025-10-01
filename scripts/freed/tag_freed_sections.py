#!/usr/bin/env python3
import json,glob
MAP={
 "Relative Functor":("2.1","Freed et al. (2024), Sec 2.1"),
 "Determinant/eta curvature":("2.6","Freed et al. (2024), Sec 2.6"),
 "Atlas swap":("2.6","Freed et al. (2024), Sec 2.6"),
 "APS split equality":("4.1","Freed et al. (2024), Sec 4.1"),
 "Relative index (volume proxy)":("4.1","Freed et al. (2024), Sec 4.1")
}
for p in glob.glob(".tau_ledger/freed/*.json") + glob.glob("analysis/freed/*.json"):
  try: d=json.load(open(p,"r",encoding="utf-8"))
  except Exception: continue
  ang=d.get("angle") or d.get("name") or d.get("Angle")
  if not ang: continue
  if "_freed_section" in d and "_freed_citation" in d: continue
  sec,cit=MAP.get(ang,("",""))
  if sec: d["_freed_section"]=sec; d["_freed_citation"]=cit; json.dump(d,open(p,"w",encoding="utf-8"),ensure_ascii=False,indent=2)
