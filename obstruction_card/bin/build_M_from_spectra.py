#!/usr/bin/env python3
import json, numpy as np, cmath
from numpy.linalg import eig, eigvals, svd, det
A=np.loadtxt("obstruction_card/out/A_full.csv",delimiter=",")
B=np.loadtxt("obstruction_card/out/B_full.csv",delimiter=",")
H0=A.dot(B); H1=B.dot(A)
def inv_sqrt(H):
    w,V=eig(H); w=np.real_if_close(w, tol=1e-10)
    w=np.array(w, dtype=float); eps=1e-14
    g=np.where(w>eps, 1.0/np.sqrt(w), 0.0)
    G=V.dot(np.diag(g)).dot(np.linalg.inv(V))
    return np.real_if_close(G, tol=1e-10)
H0m=inv_sqrt(H0); H1m=inv_sqrt(H1)
M=H0m.dot(A).dot(H1m)
np.save("obstruction_card/out/M.npy", M)
s=svd(M, compute_uv=False)
np.savetxt("obstruction_card/out/singular_values_M.csv", s[None,:], delimiter=",", fmt="%.17g")
phase=float(cmath.phase(det(M)))
with open("obstruction_card/out/detM_phase.json","w") as f: json.dump({"det_phase":phase}, f)
try:
    lam=eigvals(M); coeff=np.poly(lam)
    with open("obstruction_card/out/char_poly_coeffs.json","w") as f: json.dump({"coeff": [float(x) for x in coeff]}, f)
except Exception:
    pass
