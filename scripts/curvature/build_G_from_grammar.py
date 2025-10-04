import json, re
from pathlib import Path
def L(p,d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
def flat_str_list(x):\n  out=[]\n  if isinstance(x,str): out.append(x)\n  elif isinstance(x,list):\n    for y in x:\n      if isinstance(y,str): out.append(y)\n      elif isinstance(y,dict):\n        for k in ("name","id","sym","symbol","gen","rel"):\n          if k in y and isinstance(y[k],str): out.append(y[k])\n  return [s for s in out if s]
gram=L("etc/grammar_ci.json",{}) or {}
keys_syms=["symbols","alphabet","tokens"]; syms=[]\nfor k in keys_syms:\n  if k in gram: syms=gram.get(k) or []; break
gens=set(["id"]); rels=[]
for g in flat_str_list(gram.get("generators", [])): gens.add(g.strip())
for r in flat_str_list(gram.get("relations",  [])): rels.append(r.strip())
ren = gram.get("renamings") or gram.get("relabelings") or gram.get("renames") or []\nif isinstance(ren,dict): ren=list(ren.items())\nif isinstance(ren,list):\n  for pair in ren:\n    try:\n      a,b=(str(pair[0]),str(pair[1])) if isinstance(pair,(list,tuple)) else (str(pair),str(pair))\n      if a and b:\n        gens.add(f"swap({a},{b})"); rels.append(f"involutive(swap({a},{b}))")\n        if a not in syms: syms.append(a)\n        if b not in syms: syms.append(b)\n    except Exception: pass
safe_sym=lambda s: re.sub(r"[^A-Za-z0-9_\\-]","_",str(s))\nsyms=[safe_sym(s) for s in (syms or [])]\nsg=set()\nfor g in gens:\n  if g.startswith("swap(") and g.endswith(")"): sg.add(g)\n  else: sg.add(safe_sym(g))\nG={"domain": syms, "generators": sorted(sg), "relations": rels}\nPath("artifacts/curvature/G_presentation.json").write_text(json.dumps({"G":G},separators=(",",":")))\nprint("ok")
