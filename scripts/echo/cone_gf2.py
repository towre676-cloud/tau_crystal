import json
from pathlib import Path
def rank_gf2(A):
    m=len(A); n=len(A[0]) if m else 0
    A=[row[:] for row in A]
    r=c=0
    while r<m and c<n:
        piv=r
        while piv<m and A[piv][c]==0: piv+=1
        if piv==m: c+=1; continue
        if piv!=r: A[r],A[piv]=A[piv],A[r]
        for i in range(m):
            if i!=r and A[i][c]==1:
                for j in range(c,n): A[i][j]^=A[r][j]
        r+=1; c+=1
    return r
spec=json.loads(Path("artifacts/echo/echo_chain_nontrivial.json").read_text())
C=spec["C"]; Cp=spec["Cp"]; U=spec["U"]
dC=C["d1"]; dCp=Cp["d1"]; U1=U["U1"]; U0=U["U0"]
dC_rows=len(dC); dC_cols=len(dC[0]) if dC_rows else 0
dCp_rows=len(dCp); dCp_cols=len(dCp[0]) if dCp_rows else 0
dimC1=C["dim1"]; dimC0=C["dim0"]; dimCp1=Cp["dim1"]; dimCp0=Cp["dim0"]
dim_cone2=dimC1
dim_cone1=dimCp1+dimC0
dim_cone0=dimCp0
d2=[]
for r in range(dimCp1): d2.append(U1[r][:])
for r in range(dimC0): d2.append(dC[r][:])
if dim_cone2==0: rank_d2=0
else: rank_d2=rank_gf2(d2)
row_d1 = []
for r in range(dimCp0):
    row = []
    row += dCp[r][:] if dimCp1 else []
    row += U0[r][:] if dimC0 else []
    row_d1.append(row)
rank_d1 = rank_gf2(row_d1) if row_d1 else 0
b2 = dim_cone2 - rank_d2
b1 = (dim_cone1 - rank_d1) - rank_d2
if b1<0: b1=0
b0 = dim_cone0 - rank_d1
if b0<0: b0=0
betti=[b0,b1,b2]
Path("artifacts/echo/cone_homology_nontrivial.json").write_text(json.dumps({"betti":betti,"kmax":2},separators=(",",":")))
Path("artifacts/echo/graded_scalar_nontrivial.json").write_text(json.dumps({"graded_scalar":sum(betti),"betti":betti},separators=(",",":")))
