import os, sys, numpy as np
from python_common import write_tsv_line, sha256_path
if __name__=="__main__":
    npy=sys.argv[1]; out_tsv=sys.argv[2]
    X=np.load(npy); B=(np.sign(X)>=0).astype(np.uint8); bits=int(B.sum())
    write_tsv_line(out_tsv,["BIN", npy, sha256_path(npy), bits])
