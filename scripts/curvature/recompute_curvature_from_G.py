import json, re
from pathlib import Path
def L(p,d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
def write_safe(c_str,length,c_tokens,gens,unknown,fallback=False):\n  Path("artifacts/curvature/cocycle_cijk.json").write_text(json.dumps({"cijk":c_str,"fallback":fallback},separators=(",",":")))\n  Path("artifacts/curvature/length_metrics.json").write_text(json.dumps({"length":int(length),"reduced_word":c_tokens,"generators":sorted(list(gens)),"fallback":fallback},separators=(",",":")))\n  Path("artifacts/curvature/G_validation.json").write_text(json.dumps({"unknown_generators":sorted(list(unknown)),"fallback":fallback},separators=(",",":")))
try:
  G=L("artifacts/curvature/G_presentation.json",{"G":{"generators":["id"],"relations":[]}}).get("G",{})
  glue=L("artifacts/curvature/glue_gij.json",{"gij":[]}) or {"gij":[]}
  gens=set(G.get("generators",["id"]))
  def tokenize(word):\n    w=str(word or "id").strip()\n    if w=="id": return []\n    parts=re.split(r"[\\s·]+", w)\n    out=[]\n    for p in parts:\n      while p:\n        m=re.match(r"(swap\\([^)]*\\)|id)", p)\n        if m:\n          t=m.group(1); out.append(t); p=p[len(t):]\n        else:\n          out.append(p); break\n    return [x for x in out if x and x!="id"]
  def reduce_word(tokens):\n    out=[]\n    for t in tokens:\n      if out and out[-1]==t and t.startswith("swap("): out.pop()\n      elif t=="id": pass\n      else: out.append(t)\n    return out
  def compose(a,b): return reduce_word(a+b)
  def ok_token(t):\n    return (t in gens) or (t.startswith("swap(") and any(t==g for g in gens if str(g).startswith("swap(")))
  unknown=set(); gij=glue.get("gij",[]) or []
  def w(g):\n    toks=tokenize(g)\n    for t in toks:\n      if not ok_token(t): unknown.add(t)\n    return reduce_word(toks)
  def pick(i,j):\n    for x in gij:\n      if str(x.get("i"))==i and str(x.get("j"))==j:\n        return x.get("g","id")\n    return "id"
  g12=w(pick("U1","U2")); g23=w(pick("U2","U3")); g31=w(pick("U3","U1"))
  c = compose(compose(g12,g23),g31)\n  length=len(c); c_str="id" if length==0 else "·".join(c)\n  write_safe(c_str,length,c,gens,unknown,fallback=False)\n  print("ok")
except Exception:\n  write_safe("id",0,[],set(["id"]),set(),fallback=True)\n  print("fallback")
