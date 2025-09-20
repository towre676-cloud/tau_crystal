import os, sys, csv
from python_common import write_tsv_line
if __name__=="__main__":
    sym_tsv=sys.argv[1]; thr=float(sys.argv[2]); out_tsv=sys.argv[3]
    with open(sym_tsv, newline="", encoding="utf-8") as f:
        r=csv.reader(f, delimiter="\t")
        rows=[row for row in r]
    for row in rows:
        if len(row)<4 or row[0]=="path": continue
        npy, h, mean_str, eps_str = row
        try:
            mean=float(mean_str)
        except: continue
        if mean<=thr: write_tsv_line(out_tsv,["ANCHOR", npy, h, f"{mean:.8f}"])
