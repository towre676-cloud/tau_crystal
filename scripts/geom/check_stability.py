import os, sys, numpy as np, glob
from python_common import write_tsv_line, sha256_path
if __name__=="__main__":
    pattern=sys.argv[1]; out_tsv=sys.argv[2]
    files=sorted(glob.glob(pattern))
    if len(files)<2: sys.exit(0)
    X0=np.load(files[0]); Xm=np.load(files[-1])
    d=float(np.linalg.norm(X0 - Xm))
    write_tsv_line(out_tsv,["SPAN", files[0], files[-1], sha256_path(files[0]), sha256_path(files[-1]), f"{d:.8f}"])
