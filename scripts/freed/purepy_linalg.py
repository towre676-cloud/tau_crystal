"""Minimal pure-Python linear algebra for tiny SPD problems (n<=5).
Includes: Gram-Schmidt orthogonalization, Jacobi eigen for symmetric,
lower-Cholesky, solve via Cholesky, logdet, and a tiny PRNG-backed
orthogonal generator. Deterministic and dependency-free.
"""
import math, random
from typing import List, Tuple

Matrix = List[List[float]]

def mat_eye(n:int)->Matrix:
    return [[1.0 if i==j else 0.0 for j in range(n)] for i in range(n)]
def mat_copy(A:Matrix)->Matrix:
    return [row[:] for row in A]
def mat_T(A:Matrix)->Matrix:
    n=len(A); m=len(A[0])
    return [[A[i][j] for i in range(n)] for j in range(m)]
def mat_mul(A:Matrix,B:Matrix)->Matrix:
    n=len(A); m=len(B[0]); k=len(B)
    C=[[0.0]*m for _ in range(n)]
    for i in range(n):
        Ai=A[i]
        for p in range(k):
            a=Ai[p]; Bp=B[p]
            for j in range(m): C[i][j]+=a*Bp[j]
    return C
def mat_add(A:Matrix,B:Matrix)->Matrix:
    n=len(A); m=len(A[0])
    return [[A[i][j]+B[i][j] for j in range(m)] for i in range(n)]
def symmetrize(A:Matrix)->Matrix:
    n=len(A); S=mat_copy(A)
    for i in range(n):
        for j in range(i+1,n):
            v=0.5*(S[i][j]+S[j][i]); S[i][j]=v; S[j][i]=v
    return S

def dot(x:List[float],y:List[float])->float:
    return sum(xi*yi for xi,yi in zip(x,y))
def norm2(x:List[float])->float:
    return math.sqrt(max(0.0, dot(x,x)))

def gram_schmidt_random_orthogonal(n:int, seed:int=7)->Matrix:
    r=random.Random(seed)
    V=[[r.uniform(-1.0,1.0) for _ in range(n)] for _ in range(n)]
    Q=[[0.0]*n for _ in range(n)]
    for i in range(n):
        v=V[i][:]
        for j in range(i):
            proj = dot(v, Q[j])
            v=[v[k]-proj*Q[j][k] for k in range(n)]
        nv=norm2(v)
        if nv < 1e-12:
            # reseed row if degenerate
            v=[r.uniform(-1.0,1.0) for _ in range(n)]
            nv=norm2(v);
            if nv < 1e-12: nv=1.0
        Q[i]=[v[k]/nv for k in range(n)]
    # polish orthogonality with one symmetric re-orth step
    QT=mat_T(Q); M=mat_mul(Q,QT); E=mat_eye(n)
    # Q ← (3I - M) Q / 2  (Newton-Schulz single step for orthogonalization)
    for i in range(n):
        for j in range(n): M[i][j]=1.5*(E[i][j]) - 0.5*M[i][j]
    Qp=mat_mul(M,Q)
    return Qp

def cholesky_lower(A:Matrix)->Matrix:
    n=len(A); L=[[0.0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1):
            s = A[i][j] - sum(L[i][k]*L[j][k] for k in range(j))
            if i==j:
                if s <= 1e-15: s = 1e-15
                L[i][j]=math.sqrt(s)
            else:
                L[i][j]=s/L[j][j]
    return L
def chol_solve(L:Matrix,B:Matrix)->Matrix:
    n=len(L); m=len(B[0])
    # solve L Y = B (forward)
    Y=[[0.0]*m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            s=B[i][j] - sum(L[i][k]*Y[k][j] for k in range(i))
            Y[i][j]=s/L[i][i]
    # solve L^T X = Y (back)
    X=[[0.0]*m for _ in range(n)]
    for i in range(n-1,-1,-1):
        for j in range(m):
            s=Y[i][j] - sum(L[k][i]*X[k][j] for k in range(i+1,n))
            X[i][j]=s/L[i][i]
    return X
def logdet_from_chol(L:Matrix)->float:
    return 2.0*sum(math.log(L[i][i]) for i in range(len(L)))

def jacobi_eigh(A:Matrix, max_sweeps:int=50, tol:float=1e-12)->Tuple[List[float],Matrix]:
    # symmetric Jacobi for tiny n; returns eigenvalues ascending and Q orthogonal
    n=len(A); S=symmetrize(A); Q=mat_eye(n)
    for _ in range(max_sweeps):
        off=0.0
        p=0; q=1
        # find largest off-diagonal
        for i in range(n):
            for j in range(i+1,n):
                v=abs(S[i][j])
                if v>off: off=v; p=i; q=j
        if off < tol: break
        app=S[p][p]; aqq=S[q][q]; apq=S[p][q]
        phi=0.5*math.atan2(2.0*apq, aqq-app)
        c=math.cos(phi); s=math.sin(phi)
        # apply rotation to S
        for k in range(n):
            sk=S[k][p]; tk=S[k][q]
            S[k][p]=c*sk - s*tk
            S[k][q]=s*sk + c*tk
        for k in range(n):
            sk=S[p][k]; tk=S[q][k]
            S[p][k]=c*sk - s*tk
            S[q][k]=s*sk + c*tk
        S[p][q]=0.0; S[q][p]=0.0
        # accumulate Q
        for k in range(n):
            qk=Q[k][p]; rk=Q[k][q]
            Q[k][p]=c*qk - s*rk
            Q[k][q]=s*qk + c*rk
    vals=[S[i][i] for i in range(n)]
    # sort ascending, permute Q columns accordingly
    idx=list(range(n)); idx.sort(key=lambda i: vals[i])
    vals_sorted=[vals[i] for i in idx]
    Qs=[[Q[r][i] for i in idx] for r in range(n)]
    return vals_sorted, Qs

def trace_of_product(A:Matrix,B:Matrix)->float:
    n=len(A); s=0.0
    for i in range(n):
        for j in range(n): s+=A[i][j]*B[j][i]
    return s
