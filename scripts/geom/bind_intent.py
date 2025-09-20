import os, sys, hashlib
from python_common import write_tsv_line
if __name__=="__main__":
    geom_id=sys.argv[1]; intent_txt=sys.argv[2]; out_tsv=sys.argv[3]
    with open(intent_txt,"rb") as f: txt=f.read()
    ih=hashlib.sha256(txt).hexdigest()
    write_tsv_line(out_tsv,["INTENT", geom_id, ih])
