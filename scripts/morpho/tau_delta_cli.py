import os, sys, json, torch, numpy as np
from Src.MorphoNet.tau_delta import tau_delta_record
def read_pts(tsv):
  xs=[]; ys=[]
  for ln in open(tsv,"r",encoding="utf-8"):
    s=ln.strip().split("\t");
    if len(s)>=3 and s[0].isdigit(): xs.append(float(s[1])); ys.append(float(s[2]))
  return np.stack([xs,ys],axis=1)
def main():
  if len(sys.argv)<5: print("usage: tau_delta_cli.py pred.pt gt.tsv bb_sqrt out.json"); sys.exit(2)
  pred=torch.load(sys.argv[1], map_location="cpu")  # expects (1,68,H,W) float tensor
  gt=read_pts(sys.argv[2])
  bb=float(sys.argv[3])
  rec=tau_delta_record(pred, gt, bb)
  with open(sys.argv[4],"w",encoding="utf-8") as f: json.dump(rec,f,indent=2)
if __name__=="__main__": main()
