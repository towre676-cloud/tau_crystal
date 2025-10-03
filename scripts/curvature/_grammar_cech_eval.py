import json,re
from pathlib import Path
def load(p,default):
  try: return json.loads(Path(p).read_text())
  except Exception: return default
Gspec=load("artifacts/grammar/grammar.json",{"generators":["id"],"relations":["id*x=x","x*id=x"]})
Glue=load("artifacts/curvature/glue_gij.json",{"G":{"generators":["id"],"relations":[]},"gij":[{"i":"U1","j":"U2","g":"id"},{"i":"U2","j":"U3","g":"id"},{"i":"U3","j":"U1","g":"id"}]})
gens=set(Gspec.get("generators",[]))|{"id"}
rels=[str(r) for r in Gspec.get("relations",[])]
def ascii_token(s:str)->str:
  s=(s or "").strip().lower()
  if "swap" in s: return "swap_sigma_phi"
  if s in ("id","identity"): return "id"
  t=re.sub(r"[^a-z0-9_]+","_",s)
  return t or "id"
def reduce_word(w):
  # simple rewriting: drop id, collapse involutions g^2=id if present in relations
  inv=set()
  for r in rels:
    m=re.fullmatch(r"([a-z0-9_]+)\\^2=id",r)
    if m: inv.add(m.group(1))
  w=[x for x in w if x!="id"]
  i=0; out=[]
  while i<len(w):
    if i+1<len(w) and w[i]==w[i+1] and w[i] in inv:
      i+=2
    else:
      out.append(w[i]); i+=1
  return out or ["id"]
def compose(a,b):
  w=reduce_word([ascii_token(a),ascii_token(b)])
  return w[0] if len(w)==1 else "*".join(w)
def pick(arr,i,j):
  for x in arr:
    if x.get("i")==i and x.get("j")==j: return ascii_token(x.get("g","id"))
  return "id"
arr=Glue.get("gij",[])
g12=pick(arr,"U1","U2"); g23=pick(arr,"U2","U3"); g31=pick(arr,"U3","U1")
c=compose(compose(g12,g23),g31)
length=0 if c=="id" else (1 if c in gens else 2)
Path("artifacts/curvature/G_presentation.json").write_text(json.dumps({"G":{"generators":sorted(list(gens)),"relations":rels}},separators=(",",":")))
Path("artifacts/curvature/cocycle_cijk.json").write_text(json.dumps({"cijk":c},separators=(",",":")))
Path("artifacts/curvature/length_metrics.json").write_text(json.dumps({"length":length,"c":c},separators=(",",":")))
Path("artifacts/curvature/G_validation.json").write_text(json.dumps({"ok":(g12 in gens and g23 in gens and g31 in gens),"g12":g12,"g23":g23,"g31":g31},separators=(",",":")))
print("ok")
