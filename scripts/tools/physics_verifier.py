#!/usr/bin/env python3
import json,sys,math,hashlib,time
def die(msg): print(json.dumps({"ok":False,"error":msg}), flush=True); sys.exit(0)
if len(sys.argv)!=2: die("usage")
path=sys.argv[1]
try:
  with open(path,"r",encoding="utf-8") as f: spec=json.load(f)
except Exception as e: die(f"load_error:{e}")
m=spec.get("masses",{})
rels=spec.get("relations",[])
if not m or not rels: die("missing_masses_or_relations")
tol_default=float(spec.get("rel_tol_default",1e-3))
stamp=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
def sha256_obj(o): return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(",",":")).encode()).hexdigest()
checks=[]; all_ok=True
for r in rels:
  num=r.get("numerator"); den=r.get("denominator"); exp=r.get("expect"); tol=float(r.get("rel_tol",tol_default))
  if num not in m or den not in m or exp is None:
    checks.append({"name":r.get("name","?"),"ok":False,"error":"bad_relation_spec"}); all_ok=False; continue
  try:
    ratio=float(m[num])/float(m[den])
  except Exception as e:
    checks.append({"name":r.get("name","?"),"ok":False,"error":f"ratio_err:{e}"}); all_ok=False; continue
  rel_err=abs(ratio-exp)/exp if exp!=0 else float("inf")
  ok=rel_err<=tol
  all_ok = all_ok and ok
  checks.append({
    "name": r.get("name", f"{num}/{den}"),
    "numerator": num, "denominator": den,
    "observed": ratio, "expected": exp,
    "rel_err": rel_err, "rel_tol": tol, "ok": ok
  })
envelope={
  "ok": all_ok,
  "kind": "tau-crystal.physics.fermion_ratios",
  "timestamp": stamp,
  "input_sha256": sha256_obj(spec),
  "masses": m,
  "relations": rels,
  "checks": checks
}
print(json.dumps(envelope, separators=(",",":"), ensure_ascii=True))
