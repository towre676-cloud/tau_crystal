import os, sys, numpy as np
from python_common import write_tsv_line, sha256_path
def mirror_plane_center(X):
    c=X.mean(axis=0,keepdims=True); return c
def reflect_2d(X,c):
    Y=X-c; Y[:,0]*=-1; return Y+c
def score(X):
    c=mirror_plane_center(X); R=reflect_2d(X,c); d=np.linalg.norm(X-R, axis=1)
    eps_crit=float(np.median(d))
    return float(d.mean()), float(eps_crit)
if __name__=="__main__":
    npy=sys.argv[1]; out_tsv=sys.argv[2]
    X=np.load(npy); m,epscrit=score(X)
    write_tsv_line(out_tsv,[npy, sha256_path(npy), f"{m:.8f}", f"{epscrit:.8f}"])
