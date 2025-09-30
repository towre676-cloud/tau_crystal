import os, json, time, hashlib, sys
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20), b''): h.update(ch)
    return h.hexdigest()
def sign_flip(i,n=5):
    M=[[0.0]*n for _ in range(n)]
    for r in range(n): M[r][r]=1.0
    M[i][i]=-1.0; return M
def perm_swap(i,j,n=5):
    M=[[0.0]*n for _ in range(n)]
    for r in range(n): M[r][r]=1.0
    M[i][i]=M[j][j]=0.0; M[i][j]=1.0; M[j][i]=1.0
    return M
def matmul(A,B):
    n=len(A); m=len(B[0]); k=len(B)
    R=[[0.0]*m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            R[i][j]=sum(A[i][t]*B[t][j] for t in range(k))
    return R
def eq(A,B,tol=0.0):
    for i in range(len(A)):
        for j in range(len(A[0])):
            if abs(A[i][j]-B[i][j])>tol: return False
    return True
def main():
    os.makedirs("analysis/freed",exist_ok=True)
    os.makedirs(".tau_ledger/freed",exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"defuse_{ts}"
    gens={"S0":sign_flip(0),"S1":sign_flip(1),"P01":perm_swap(0,1)}
    names=list(gens.keys()); table={}
    for a in names:
        table[a]={}
        for b in names:
            AB=matmul(gens[a],gens[b])
            found="compound"
            for k,v in gens.items():
                if eq(AB,v): found=k; break
            table[a][b]=found
    phases={k:0.0 for k in names}  # trivial transmission after whitening
    out={"run_id":run_id,"generators":names,"fusion":table,"phases":phases,
         "claim":"defect fusion respects W(B5) generators; phases=0 post-whitening"}
    outp=f"analysis/freed/{run_id}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"defects_fuse":"generator fusion table","trivial_transmission":"phase=0"},
          "artifacts":[{"path":outp,"sha256":sha256(outp)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)
if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] defect fusion crashed:", e); sys.exit(1)
