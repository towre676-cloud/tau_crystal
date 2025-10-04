import json
from pathlib import Path
from typing import List, Tuple
from snf_int import snf_diag

def L(p, d=None):
    try: return json.loads(Path(p).read_text())
    except Exception: return d

def shape(M: List[List[int]]) -> Tuple[int,int]:
    return (len(M), len(M[0]) if M and isinstance(M[0], list) else 0)

def zeros(r: int, c: int) -> List[List[int]]:
    return [[0]*c for _ in range(r)]

def pad(M, r, c):
    R,C = shape(M)
    Z = zeros(r,c)
    for i in range(min(R,r)):
        for j in range(min(C,c)):
            Z[i][j] = int(M[i][j])
    return Z

def dims_from_boundaries(d2, d1, d0):
    # infer dim C2,C1,C0 (or Dk) from boundary shapes (cols of d_k)
    def cols(M): return shape(M)[1]
    def rows(M): return shape(M)[0]
    n2 = cols(d2)
    n1 = cols(d1)
    n0 = cols(d0)
    # backfill via rows if missing
    if n1==0 and rows(d2)>0: n1 = rows(d2)
    if n0==0 and rows(d1)>0: n0 = rows(d1)
    return {2:n2,1:n1,0:n0}

def build_cone_differentials(C, D, U):
    # d^C_k, d^D_k
    dC2 = C.get("d2", []); dC1 = C.get("d1", []); dC0 = C.get("d0", [])
    dD2 = D.get("d2", []); dD1 = D.get("d1", []); dD0 = D.get("d0", [])
    dimsC = dims_from_boundaries(dC2, dC1, dC0)
    dimsD = dims_from_boundaries(dD2, dD1, dD0)
    # U_k: C_k -> D_k  (expect U2,U1,U0)
    U2 = U.get("U2", []); U1 = U.get("U1", []); U0 = U.get("U0", [])

    # Cone_k = D_k ⊕ C_{k-1}; differential:
    # d_cone,k = [[ dD_k , U_{k-1} ],
    #             [   0   , -dC_{k-1}] ] : (D_k ⊕ C_{k-1}) -> (D_{k-1} ⊕ C_{k-2})
    cone = {}

    # k=2
    dDk, Ukm1, dCkm1 = dD2, U1, dC1
    rTL, cTL = shape(dDk)
    rTR, cTR = shape(Ukm1)
    rBR, cBR = shape(dCkm1)
    # top: rTL x (cTL + cTR); bottom: rBR x (cTL + cTR)
    TL = pad(dDk, rTL, cTL)
    TR = pad(Ukm1, rTL, cTR)
    BL = zeros(rBR, cTL)
    BR = pad([[-x for x in row] for row in dCkm1], rBR, cBR)
    d2 = [ TL[i] + TR[i] for i in range(rTL) ] + [ BL[i] + BR[i] for i in range(rBR) ]
    cone["d2"] = d2

    # k=1
    dDk, Ukm1, dCkm1 = dD1, U0, dC0
    rTL, cTL = shape(dDk)
    rTR, cTR = shape(Ukm1)
    rBR, cBR = shape(dCkm1)
    TL = pad(dDk, rTL, cTL)
    TR = pad(Ukm1, rTL, cTR)
    BL = zeros(rBR, cTL)
    BR = pad([[-x for x in row] for row in dCkm1], rBR, cBR)
    d1 = [ TL[i] + TR[i] for i in range(rTL) ] + [ BL[i] + BR[i] for i in range(rBR) ]
    cone["d1"] = d1

    # k=0
    # maps to Cone_{-1}; only keep matrix shape for rank calc (empty here)
    cone["d0"] = D.get("d0", [])  # harmless placeholder
    return cone

def rank_from_diag(diag): 
    return sum(1 for x in diag if int(x)!=0)

def betti_from_snf(diag_next, diag_curr, n_curr):
    r_d  = rank_from_diag(diag_curr)
    r_im = rank_from_diag(diag_next)
    b = (n_curr - r_d) - r_im
    return int(b) if b>0 else 0

def cols(M): 
    return len(M[0]) if M and isinstance(M[0], list) and M[0] else 0

# Load inputs
C = L("artifacts/echo/chain_Z_C.json", {}) or {}
D = L("artifacts/echo/chain_Z_D.json", {}) or {}
U = L("artifacts/echo/U_chain_Z.json",  {}) or {}

cone = build_cone_differentials(C,D,U)
d2 = cone.get("d2", []); d1 = cone.get("d1", []); d0 = cone.get("d0", [])

diag2, r2 = snf_diag(d2)
diag1, r1 = snf_diag(d1)
diag0, r0 = snf_diag(d0)

# dims of Cone_k = cols(d_k)
n0 = cols(d0); n1 = cols(d1); n2 = cols(d2)

b0 = betti_from_snf(diag1, diag0, n0)
b1 = betti_from_snf(diag2, diag1, n1)
b2 = betti_from_snf([],    diag2, n2)

# torsion_upper: non-unit diagonal entries of d_{k+1} (upper bound on torsion in H_k)
def torsion_upper(diag):
    return [int(x) for x in diag if int(x) not in (0,1,-1)]

out_snf = {
  "d2": {"diag": diag2, "rank": r2},
  "d1": {"diag": diag1, "rank": r1},
  "d0": {"diag": diag0, "rank": r0}
}
Path("artifacts/echo/cone_snf_diagonals.json").write_text(json.dumps(out_snf, separators=(",",":")))
Path("artifacts/echo/cone_homology_Zplus.json").write_text(json.dumps({
    "betti":[b0,b1,b2],
    "torsion_upper":{"H0": torsion_upper(diag1), "H1": torsion_upper(diag2), "H2":[]},
    "notes":"torsion_upper is an auditor-safe upper bound; equals [] in the tiny identity case"
}, separators=(",",":")))
print("ok")
