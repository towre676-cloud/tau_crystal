#!/usr/bin/env python3
import os, json, re, hashlib, csv, time
from pathlib import Path
def canon(d):
  b=json.dumps(d,sort_keys=True,separators=(",",":")).encode("utf-8")
  return hashlib.sha256(b).hexdigest()
def conf_from_logs(p):
  for d in [p.parent, p.parent.parent]:
    if (not d) or (not d.exists()):
      continue
    best=None; mt=-1.0
    for q in d.iterdir():
      name=q.name.lower()
      if q.suffix.lower() not in [".log",".txt"]:
        continue
      if "face" not in name:
        continue
      try:
        s=q.read_text(encoding="utf-8",errors="ignore")
      except Exception:
        continue
      m=re.findall(r"confidence\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)", s, re.I)
      if not m:
        continue
      try:
        t=q.stat().st_mtime
      except Exception:
        t=time.time()
      if t>mt:
        mt=t; best=float(m[-1])
    if best is not None:
      return best
  return None
def tier(c):
  if c is None:
    return "unknown"
  if c>=0.99: return "0.99-1.00"
  if c>=0.97: return "0.97-0.99"
  if c>=0.95: return "0.95-0.97"
  return "<0.95"
def main():
  root=Path(".").resolve()
  out=(root/".tau_ledger"/"census")
  out.mkdir(parents=True,exist_ok=True)
  seen={}
  for dp,_,fns in os.walk(root):
    base=os.path.basename(dp)
    if base in {".git",".lake","node_modules"}:
      continue
    if "face_trace.json" not in fns:
      continue
    p=Path(dp)/"face_trace.json"
    try:
      d=json.loads(p.read_text(encoding="utf-8"))
    except Exception:
      continue
    sig=d.get("face_signature")
    h=sig if isinstance(sig,str) and len(sig)>=16 else canon(d)
    c=d.get("face_confidence")
    try:
      c=float(c)
    except Exception:
      c=None
    if c is None:
      c=conf_from_logs(p)
    try:
      mt=p.stat().st_mtime
    except Exception:
      mt=0.0
    row={"hash":h,"confidence":c,"tier":tier(c),"source_path":str(p.relative_to(root))}
    score=(c if c is not None else -1.0, mt)
    if (h not in seen) or (score>seen[h][0]):
      seen[h]=(score,row)
  rows=[v[1] for v in seen.values()]
  rows.sort(key=lambda r:( {"0.99-1.00":0,"0.97-0.99":1,"0.95-0.97":2,"unknown":3,"<0.95":4}.get(r["tier"],9), -(r["confidence"] or -1)))
  with (out/"census.tsv").open("w",encoding="utf-8",newline="") as f:
    w=csv.writer(f,delimiter="\t")
    w.writerow(["hash","confidence","tier","source_path"])
    for r in rows:
      w.writerow([r["hash"],r["confidence"],r["tier"],r["source_path"]])
  counts={}
  for r in rows:
    counts[r["tier"]]=counts.get(r["tier"],0)+1
  with (out/"summary.tsv").open("w",encoding="utf-8",newline="") as f:
    w=csv.writer(f,delimiter="\t")
    w.writerow(["tier","count"])
    for k in ["0.99-1.00","0.97-0.99","0.95-0.97","unknown","<0.95"]:
      if k in counts:
        w.writerow([k,counts[k]])
  print(f"[census] rows={len(rows)} out={out}")
  for r in rows[:5]:
    print(" -",r["hash"],r["confidence"],r["tier"],r["source_path"])
if __name__=="__main__":
  main()
