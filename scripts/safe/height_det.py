import sys,io,csv,json,math
rec,mx,out = sys.argv[1], sys.argv[2], sys.argv[3]
pairs=set(); vals={}
with io.open(mx,"r",encoding="utf-8") as f:
  rd=csv.reader(f)
  for i,row in enumerate(rd):
    if i==0 or not row or row[0].startswith("#"): continue
    try: a,b = int(row[0]), int(row[1]); v = float(row[2])
    except: continue
    pairs.add(a); pairs.add(b); vals[(a,b)] = v; vals[(b,a)] = v
idx = sorted(pairs)
n=len(idx)
M=[[0.0]*n for _ in range(n)]
pos={k:i for i,k in enumerate(idx)}
for (a,b),v in vals.items(): M[pos[a]][pos[b]]=v
# naive determinant (Gaussian elimination) to avoid numpy
det=1.0
for i in range(n):
  # pivot
  piv=i; mxv=abs(M[i][i])
  for r in range(i+1,n):
    if abs(M[r][i])>mxv: piv=r; mxv=abs(M[r][i])
  if mxv==0.0: det=0.0; break
  if piv!=i: M[i],M[piv]=M[piv],M[i]; det*=-1
  pivv=M[i][i]; det*=pivv
  # eliminate
  for r in range(i+1,n):
    if M[r][i]==0.0: continue
    f=M[r][i]/pivv
    for c in range(i,n): M[r][c]-=f*M[i][c]
with io.open(rec,"r",encoding="utf-8") as f: R=json.load(f)
R.setdefault("curve",{}).update({"regulator_det":det,"height_matrix_size":n})
with io.open(rec,"w",encoding="utf-8") as f: f.write(json.dumps(R,separators=(",",":"))+"\n")
with io.open(out,"w",encoding="utf-8") as f: f.write(json.dumps({"size":n,"det":det},separators=(",",":"))+"\n")
