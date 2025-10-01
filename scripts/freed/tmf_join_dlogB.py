#!/usr/bin/env python3
import json,glob,time,math
levels=sorted(glob.glob("analysis/freed/tmf_level_*.json"))
rows=[]
for p in levels:
  try: d=json.load(open(p,"r",encoding="utf-8"))
  except Exception: continue
  N=None
  for k in ("level","N","mod_level"):
    if k in d and isinstance(d[k],(int,float)): N=int(d[k])
  dlog=None
  for k in ("Delta_logB","delta_logB","dlogB","d_logB"):
    if k in d and isinstance(d[k],(int,float)): dlog=float(d[k])
  if N is None or dlog is None: continue
  rows.append({"level":N,"Delta_logB":dlog,"_file":p})
rows=sorted(rows,key=lambda r:r["level"])
stability=None
if rows:
  m=sum(r["Delta_logB"] for r in rows)/len(rows)
  var=sum((r["Delta_logB"]-m)**2 for r in rows)/len(rows)
  stability={"count":len(rows),"mean":m,"std":math.sqrt(var)}
out={"angle":"TMF stability","rows":rows,"stability":stability,
     "_freed_section":"2.6","_freed_citation":"Freed et al. (2024), Sec 2.6"}
dst="analysis/freed/tmf_deltas_join_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(out,open(dst,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(dst)
