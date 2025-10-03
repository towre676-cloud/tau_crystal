import json,os
from pathlib import Path
out={}
def load(p):
    try: return json.loads(Path(p).read_text())
    except: return None
out["echo_identity"]={
  "chain": load("artifacts/echo/echo_chain.json"),
  "homology": load("artifacts/echo/cone_homology.json"),
  "graded": load("artifacts/echo/graded_scalar.json")}
out["echo_nontrivial"]={
  "chain": load("artifacts/echo/echo_chain_nontrivial.json"),
  "homology": load("artifacts/echo/cone_homology_nontrivial.json"),
  "graded": load("artifacts/echo/graded_scalar_nontrivial.json")}
print(json.dumps(out,separators=(",",":")))
