import json, math
def to_c(x):
    if isinstance(x, (int, float)): return complex(float(x), 0.0)
    if isinstance(x, list) and len(x)==2: return complex(float(x[0]), float(x[1]))
    raise TypeError("T entries must be real or [Re,Im]")
D = json.load(open("analysis/modular/mod_canon.json", "r", encoding="utf-8"))
S = [[complex(float(x)) for x in row] for row in D["S"]]
Traw = D["T"]
n = len(S); assert all(len(r)==n for r in S)
T = [[0]*n for _ in range(n)]
for i in range(n):
    for j in range(n):
        T[i][j] = 0j if i!=j else to_c(Traw[i][j])
def hc(A): return [[A[j][i].conjugate() for j in range(n)] for i in range(n)]
def mm(A,B): return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def eye(): return [[1 if i==j else 0 for j in range(n)] for i in range(n)]
def diagmul(A,D): return [[A[i][j]*D[j][j] for j in range(n)] for i in range(n)]
def near(A,B,eps=1e-9):
    for i in range(n):
        for j in range(n):
            if abs(A[i][j]-B[i][j])>eps: return False
    return True
# Unitary S
I = eye(); ShS = mm(hc(S), S); assert near(ShS, I), "S not unitary"
# T diagonal phases
for i in range(n):
    for j in range(n):
        if i!=j: assert abs(T[i][j])<1e-12
for i in range(n):
    r = abs(T[i][i]); assert abs(r-1)<1e-9, "T diag not unit modulus"
# Verlinde integers
N = [[[0]*n for _ in range(n)] for _ in range(n)]
for i in range(n):
  for j in range(n):
    for k in range(n):
      num = sum(S[i][m]*S[j][m]*S[k][m].conjugate()/S[0][m] for m in range(n))
      assert abs(num.imag) < 1e-8, "Verlinde not real"
      N[i][j][k] = round(num.real)
      assert abs(num.real - N[i][j][k]) < 1e-6, "Verlinde not close to integer"
# Braid relation S^2=(ST)^3
ST = mm(S, diagmul(eye(), T))
ST3 = mm(mm(ST, ST), ST)
S2 = mm(S, S)
assert near(S2, ST3, 1e-6), "braid S^2!=(ST)^3"
print("[ok] modular: unitary S, phase-diagonal T, Verlinde integers, braid relation")
