import json
from pathlib import Path
def L(p,d=None):
    try: return json.loads(Path(p).read_text())
    except Exception: return d

w={}
# Cone(id) witness: prefer Zplus -> Z -> GF(2)
bZp = (L("artifacts/echo/cone_homology_Zplus.json",{}) or {}).get("betti")
bZ  = (L("artifacts/echo/cone_homology_Z.json",{}) or {}).get("betti")
b2  = (L("artifacts/echo/cone_homology.json",{}) or {}).get("betti")
cone_ok = (isinstance(bZp,list) and all(int(x)==0 for x in bZp)) \
       or (isinstance(bZ,list)  and all(int(x)==0 for x in bZ)) \
       or (isinstance(b2,list)  and all(int(x)==0 for x in b2))
w["ConeIdAcyclic"]={"ok":bool(cone_ok),"betti_Zplus":bZp,"betti_Z":bZ,"betti_GF2":b2}

# Čech identities witness
c  = L("artifacts/curvature/cocycle_cijk.json",{}) or {}
val= L("artifacts/curvature/G_validation.json",{}) or {}
unk= (val or {}).get("unknown_generators",[])
w["CechIdentities"]={"ok":bool(("cijk" in c) and (not unk)), "unknown_generators":unk, "has_c":("cijk" in c)}

Path("artifacts/audit/proofs_index.json").write_text(json.dumps(w,separators=(",",":")))
print("ok")
