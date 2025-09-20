import os, sys, numpy as np
from scipy.io import loadmat
from python_common import sha256_path, write_tsv_line
def pick_landmarks(S):
    keys=[k for k in S.keys() if not k.startswith("__")]
    for k in keys:
        V=S[k]
        if isinstance(V, np.ndarray) and V.ndim<=3 and V.size>0:
            A=V.squeeze()
            if A.ndim==2 and (A.shape[1] in (2,3) or A.shape[0] in (2,3)):
                if A.shape[0] in (2,3): A=A.T
                return A.astype(np.float64)
    raise RuntimeError("no landmark-like array found")
def procrustes_canon(X):
    X=X - X.mean(axis=0, keepdims=True)
    s=np.linalg.norm(X)
    X=X/(s+1e-12)
    return X
def main(in_path,out_dir,receipt_tsv):
    raw_hash=sha256_path(in_path)
    S=loadmat(in_path, squeeze_me=True, struct_as_record=False)
    X=pick_landmarks(S)
    Xc=procrustes_canon(X)
    base=os.path.splitext(os.path.basename(in_path))[0]
    os.makedirs(out_dir, exist_ok=True)
    npy=os.path.join(out_dir, base+".canon.npy")
    np.save(npy, Xc)
    out_hash=sha256_path(npy)
    write_tsv_line(receipt_tsv,[in_path, raw_hash, npy, out_hash])
if __name__=="__main__":
    ip=sys.argv[1]; od=sys.argv[2]; rt=sys.argv[3]; main(ip,od,rt)
