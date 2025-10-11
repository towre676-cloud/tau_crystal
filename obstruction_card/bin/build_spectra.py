#!/usr/bin/env python3
import json, numpy as np, sys
A=np.loadtxt("obstruction_card/out/A_full.csv",delimiter=",")
B=np.loadtxt("obstruction_card/out/B_full.csv",delimiter=",")
H0=A.dot(B); H1=B.dot(A)
e0=np.linalg.eigvals(H0); e1=np.linalg.eigvals(H1)
def to_real(x): return float(np.real_if_close(x, tol=1e-10))
with open("obstruction_card/out/spectra_H0.json","w") as f: json.dump({"eigenvalues":[to_real(z) for z in e0]},f)
with open("obstruction_card/out/spectra_H1.json","w") as f: json.dump({"eigenvalues":[to_real(z) for z in e1]},f)
