import os, sys, numpy as np
from python_common import sha256_path, write_tsv_line
def procrustes(A,B):
    A=A-A.mean(0); B=B-B.mean(0)
    A=A/(np.linalg.norm(A)+1e-12); B=B/(np.linalg.norm(B)+1e-12)
    U,_,Vt=np.linalg.svd(A.T@B); R=U@Vt; return float(np.linalg.norm(A@R - B))
if __name__=="__main__":
    anchor_npy=sys.argv[1]; cand_npy=sys.argv[2]; tau=float(sys.argv[3]); out_tsv=sys.argv[4]
    A=np.load(anchor_npy); B=np.load(cand_npy); d=procrustes(A,B)
    decision="VERIFY" if d<=tau else "REJECT"
    write_tsv_line(out_tsv,[decision, anchor_npy, sha256_path(anchor_npy), cand_npy, sha256_path(cand_npy), f"{d:.8f}", f"{tau:.8f}"])
