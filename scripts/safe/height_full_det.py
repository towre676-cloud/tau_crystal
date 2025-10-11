import sys,io,json
rec,mx,out = sys.argv[1], sys.argv[2], sys.argv[3]
rows=[]
for line in io.open(mx,"r",encoding="utf-8"):
    s=line.strip()
    if not s or s.startswith("#"): continue
    rows.append([float(x) for x in s.split(",") if x.strip()!=""])
n=len(rows)
assert all(len(r)==n for r in rows), "matrix must be square"
M=[r[:] for r in rows]
det=1.0
for i in range(n):
    piv=i; mxv=abs(M[i][i])
    for r in range(i+1,n):
        if abs(M[r][i])>mxv: piv=r; mxv=abs(M[r][i])
    if mxv==0.0: det=0.0; break
    if piv!=i: M[i],M[piv]=M[piv],M[i]; det*=-1
    pivv=M[i][i]; det*=pivv
    for r in range(i+1,n):
        if M[r][i]==0.0: continue
        f=M[r][i]/pivv
        for c in range(i,n): M[r][c]-=f*M[i][c]
R=json.load(io.open(rec,"r",encoding="utf-8"))
R.setdefault("curve",{}).update({"regulator_det":det,"height_matrix_size":n})
io.open(rec,"w",encoding="utf-8").write(json.dumps(R,separators=(",",":"))+"\n")
io.open(out,"w",encoding="utf-8").write(json.dumps({"size":n,"det":det},separators=(",",":"))+"\n")
