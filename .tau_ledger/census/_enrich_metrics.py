#!/usr/bin/env python3
import csv, json, re
from pathlib import Path
def find_metrics(start):
  conv=None; sym=None
  for d in [start.parent, start.parent.parent]:
    if not d or not d.exists(): continue
    for p in d.iterdir():
      name=p.name.lower(); suf=p.suffix.lower()
      if suf==".json" and ("metric" in name or "fusion" in name or "face" in name):
        try:
          data=json.load(open(p,"r",encoding="utf-8"))
          for k,v in data.items():
            lk=k.lower()
            if conv is None and "convexity" in lk:
              try: conv=float(v)
              except: pass
            if sym is None and "rms" in lk and ("symmetry" in lk or "bilateral" in lk):
              try: sym=float(v)
              except: pass
        except: pass
      if suf in [".tsv",".csv"] and ("metric" in name or "face" in name):
        try:
          with open(p,"r",encoding="utf-8",errors="ignore") as f:
            head=f.readline(); sep="\t" if "\t" in head else ","
            cols=[c.strip().lower() for c in head.strip().split(sep)]
            iC=next((i for i,c in enumerate(cols) if "convexity" in c),None)
            iS=next((i for i,c in enumerate(cols) if "rms" in c and ("symmetry" in c or "bilateral" in c)),None)
            for line in f:
              parts=[x.strip() for x in line.strip().split(sep)]
              if conv is None and iC is not None and iC < len(parts):
                try: conv=float(parts[iC])
                except: pass
              if sym is None and iS is not None and iS < len(parts):
                try: sym=float(parts[iS])
                except: pass
        except: pass
      if suf in [".log",".txt"] and "face" in name:
        try:
          for line in open(p,"r",encoding="utf-8",errors="ignore"):
            if conv is None:
              m=re.search(r"convexity\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)", line, re.I)
              if m: conv=float(m.group(1))
            if sym is None:
              m=re.search(r"(symmetry|bilateral).*?rms\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)", line, re.I)
              if m: sym=float(m.group(m.lastindex))
        except: pass
  return conv, sym
def main():
  root=Path(".").resolve()
  census=root/".tau_ledger"/"census"/"census.tsv"
  out=root/".tau_ledger"/"census"/"census_full.tsv"
  rows=[]
  with open(census,"r",encoding="utf-8") as f:
    rd=csv.reader(f,delimiter="\t")
    hdr=next(rd,None)
    for h in rd:
      rows.append({"hash":h[0],"confidence":h[1] or None,"tier":h[2],"source_path":h[3]})
  for r in rows:
    p=(root/r["source_path"]).resolve()
    conv,sym=find_metrics(p)
    r["convexity_deg"]=conv
    r["symmetry_rms"]=sym
  with open(out,"w",encoding="utf-8",newline="") as f:
    wr=csv.writer(f,delimiter="\t")
    wr.writerow(["hash","convexity_deg","symmetry_rms","confidence","tier","source_path"])
    for r in rows:
      wr.writerow([r["hash"],r["convexity_deg"],r["symmetry_rms"],r["confidence"],r["tier"],r["source_path"]])
  print("[enrich] wrote", out)
if __name__=="__main__": main()
