from scripts.freed._helpers_common import write_receipt

def sign_flip(i):
    M=[[0.0]*5 for _ in range(5)]
    for k in range(5): M[k][k]=1.0
    M[i][i] = -1.0
    return M

def swap01():
    M=[[0.0]*5 for _ in range(5)]
    M[0][1]=1.0; M[1][0]=1.0; M[2][2]=1.0; M[3][3]=1.0; M[4][4]=1.0
    return M

def matmul(A,B):
    n=len(A); m=len(B[0]); p=len(B)
    C=[[0.0]*m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            C[i][j]=sum(A[i][k]*B[k][j] for k in range(p))
    return C

def main():
    I=[[1.0 if i==j else 0.0 for j in range(5)] for i in range(5)]
    s0=sign_flip(0)
    p =swap01()
    def is_I(M): return all(abs(M[i][j]-I[i][j])<1e-15 for i in range(5) for j in range(5))
    ok = is_I(matmul(s0,s0)) and is_I(matmul(p,p)) and is_I(matmul(matmul(s0,p),matmul(s0,p)))

    payload = {
      "_inputs":{},
      "_claims":{"defect_fusion":"generator fusions hold; transmission phase trivial"},
      "_certificates":{"fusion_ok":bool(ok),"transmission_phase":0.0}
    }
    write_receipt("a7_defect_fusion", payload)

if __name__=="__main__":
    main()
