#!/usr/bin/env python3
import json,glob,time
files=sorted(glob.glob("analysis/freed/defect_*.json"))
table=[]; phases=[]
for p in files:
  try: d=json.load(open(p,"r",encoding="utf-8"))
  except Exception: continue
  phase=None
  for path in (("phase",),("phases",),("fusion","phase"),("whitened","phase")):
    cur=d; ok=True
    for k in path:
      if isinstance(cur,dict) and k in cur: cur=cur[k]
      else: ok=False; break
    if ok and isinstance(cur,(int,float)):
      phase=float(cur); table.append({"file":p,"phase":phase}); phases.append(phase); break
all_zero=bool(phases) and all(abs(x)<=1e-12 for x in phases)
out={"angle":"Defect fusion","fusion_table":table,
     "all_phases_zero_after_whitening":all_zero,
     "_freed_section":"2.9","_freed_citation":"Freed et al. (2024), Sec 2.9"}
dst=".tau_ledger/freed/defect_fusion_table_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(out,open(dst,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(dst)
