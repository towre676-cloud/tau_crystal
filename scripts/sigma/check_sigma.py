import json
from pathlib import Path
sig=json.loads(Path("etc/sigma_signature.json").read_text())
ops=sig["ops"]
def ok_op(op,argc): return (op in ops) and (argc==ops[op]["arity"])
def reduce_compose(a,b):
  if a=="id": return b
  if b=="id": return a
  return f"compose({a},{b})"
p=Path("artifacts/sigma/terms.jsonl")
lines=p.read_text().splitlines() if p.exists() else []
valid=[]; invalid=[]; reduced=[]
for ln in lines:
  try:
    j=json.loads(ln); op=j.get("op"); args=j.get("args",[])
    (valid if ok_op(op,len(args)) else invalid).append(j)
    if op=="compose" and len(args)==2: reduced.append({"in":args,"out":reduce_compose(args[0],args[1])})
  except Exception:
    invalid.append({"raw":ln,"error":"json"})
assoc_ok=True
triples=[("id","id","x"),("x","id","y"),("x","y","id")]
for x,y,z in triples:
  left=reduce_compose(reduce_compose(x,y),z)
  right=reduce_compose(x,reduce_compose(y,z))
  if left!=right: assoc_ok=False
out={"signature":"etc/sigma_signature.json","counts":{"valid":len(valid),"invalid":len(invalid)},"assoc_ok":assoc_ok,"reductions":reduced}
Path("artifacts/sigma/sigma_laws.json").write_text(json.dumps(out,separators=(",",":")))
print("ok")
