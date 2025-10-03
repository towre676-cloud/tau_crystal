import json,csv,sys
from pathlib import Path
root=Path(".")
def load_weights():
  try: return json.loads(Path("etc/echo_filt.json").read_text()).get("weights",{})
  except Exception: return {}
def pick_file():
  for p in [root/"data/qcro_counts.json",root/"data/qcro_counts.csv",root/"data/qcro_counts.tsv"]:
    if p.exists() and p.stat().st_size>0: return p
  return None
def from_json(p):
  j=json.loads(Path(p).read_text())
  if isinstance(j,dict): return {str(k):float(j[k]) for k in j}
  if isinstance(j,list):
    out={};
    for r in j:
      if isinstance(r,dict):
        k=str(r.get("symbol") or r.get("token") or r.get("k") or r.get("name"))
        v=float(r.get("count") or r.get("v") or r.get("n") or 0)
        out[k]=out.get(k,0.0)+v
    return out
  raise ValueError("bad JSON format")
def from_table(p,delim):
  with open(p,"r",newline="") as f:
    r=csv.DictReader(f,delimiter=delim)
    out={}
    # pick first non-numeric column name as key if needed
    fields=r.fieldnames or []
    keyc=None
    for c in fields:
      if c.lower() in ("symbol","token","name","k"): keyc=c; break
    if keyc is None:
      # assume first column is key
      keyc = fields[0] if fields else None
    valc=None
    for c in fields:
      if c.lower() in ("count","v","n","value"): valc=c; break
    if valc is None:
      # try any other column as numeric
      for c in fields[1:]:
        try: float(next(csv.DictReader(open(p)).__next__()[c])); valc=c; break
        except Exception: continue
    for row in r:
      try:
        k=str(row[keyc]) if keyc else "unknown"
        v=float(row[valc]) if valc else 0.0
        out[k]=out.get(k,0.0)+v
      except Exception: pass
    return out
def load_counts():
  p=pick_file()
  if p is None: return {}
  if str(p).endswith(".json"): return from_json(p)
  if str(p).endswith(".csv"):  return from_table(p,",")
  if str(p).endswith(".tsv"):  return from_table(p,"\\t")
  return {}
def graded(norm,weights):
  g=0.0
  for k,p in norm.items(): g+=float(weights.get(k,1.0))*float(p)
  return g
counts=load_counts(); total=sum(counts.values()) if counts else 0.0
norm={k:(v/total if total>0 else 0.0) for k,v in counts.items()}
weights=load_weights(); g=graded(norm,weights)
Path("artifacts/echo/qcro_hist_raw.json").write_text(json.dumps({"counts":counts,"total":total},separators=(",",":")))
Path("artifacts/echo/qcro_hist_norm.json").write_text(json.dumps({"norm":norm},separators=(",",":")))
Path("artifacts/echo/graded_scalar_from_hist.json").write_text(json.dumps({"graded_scalar":g,"weights":weights},separators=(",",":")))
print("ok")
