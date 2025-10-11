#!/usr/bin/env python3
import numpy as np, json, os, sys
od=os.path.join("obstruction_card","out")
A=np.loadtxt(os.path.join(od,"A_full.csv"),delimiter=",")
B=np.loadtxt(os.path.join(od,"B_full.csv"),delimiter=",")
H0=A.dot(B); H1=B.dot(A)
e0=np.linalg.eigvals(H0); e1=np.linalg.eigvals(H1)
def pack(e): return {"eigvals":[(x.real if abs(x.imag)<1e-15 else [x.real,x.imag]) for x in e]}
json.dump(pack(e0), open(os.path.join(od,"spectra_H0.json"),"w"))
json.dump(pack(e1), open(os.path.join(od,"spectra_H1.json"),"w"))
