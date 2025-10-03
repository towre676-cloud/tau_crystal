import json
def rank(A):
    m=len(A); n=len(A[0]) if m else 0
    A=[r[:] for r in A]; r=c=0
    while r<m and c<n:
        p=r
        while p<m and A[p][c]==0: p+=1
        if p==m: c+=1; continue
        if p!=r: A[r],A[p]=A[p],A[r]
        for i in range(m):
            if i!=r and A[i][c]==1:
                for j in range(c,n): A[i][j]^=A[r][j]
        r+=1; c+=1
    return r
# C•: C1 -> C0 with d=0; U=id
dC=[[0]]; U1=[[1]]; U0=[[1]]
dimC1=1; dimC0=1; dimCp1=1; dimCp0=1
dim_cone2=dimC1
dim_cone1=dimCp1+dimC0
dim_cone0=dimCp0
d2 = U1 + dC  # block rows
rank_d2 = rank(d2)
row_d1 = [[1,1]]  # [dCp|U0] with dCp=1, U0=1
rank_d1 = rank(row_d1)
b2 = dim_cone2 - rank_d2
b1 = (dim_cone1 - rank_d1) - rank_d2
b0 = dim_cone0 - rank_d1
w={"betti":[b0,b1,b2],"expect":[0,0,0],"ok":(b0==0 and b1==0 and b2==0)}
open("artifacts/proofs/cone_id_gf2.json","w").write(json.dumps(w,separators=(",",":")))
