import os, re, json, math, pathlib, csv
from typing import Dict, Tuple, List
AP_OUT=".tau_ledger/langlands/ap.json"; SA_OUT=".tau_ledger/langlands/satake.json"
META_DEFAULT={"k":0,"N":1,"sources":[]}
CANDIDATES=[
  ".tau_ledger/langlands/L_tau.json",
  ".tau_ledger/langlands/rank.json",
  ".tau_ledger/langlands/ap.json",
  ".tau_ledger/experimental/fft_bsd.json",
]
def _load_json(path):
  try: return json.load(open(path,encoding="utf-8"))
  except Exception: return {}
def harvest_from_json()->Tuple[Dict[int,float],dict,List[str]]:
  ap:Dict[int,float]={}; meta=dict(META_DEFAULT); sources:List[str]=[]
  for p in CANDIDATES:
    if os.path.isfile(p):
      d=_load_json(p)
      if "ap" in d and isinstance(d["ap"],dict):
        for k,v in d["ap"].items():
          try: ap[int(k)]=float(v)
          except Exception: pass
        sources.append(p+":ap")
      for key in ("level","N","weight","k"):
        if key in d:
          if key in ("level","N"): meta["N"]=int(d[key])
          if key in ("weight","k"): meta["k"]=int(d[key])
  return ap,meta,sources
def primes_up_to(n:int)->List[int]:
  if n<2: return []
  bs=[True]*(n+1); bs[0]=bs[1]=False
  for p in range(2,int(n**0.5)+1):
    if bs[p]:
      step=p; start=p*p
      bs[start:n+1:step]=[False]*(((n-start)//step)+1)
  return [i for i,b in enumerate(bs) if b]
def harvest_from_tau_csv(meta)->Tuple[Dict[int,float],List[str]]:
  ap={}; sources=[]
  p=pathlib.Path(".tau_ledger/seq/tau.csv")
  if not p.exists(): return ap,sources
  rows=open(p,encoding="utf-8").read().strip().splitlines()
  if not rows: return ap,sources
  # Try to parse "n,value" with header
  for i,line in enumerate(rows):
    if i==0 and not re.match(r"^[0-9]+[,\\s]", line): continue
    parts=[x.strip() for x in line.split(",")]
    if len(parts)>=2 and parts[0].isdigit():
      n=int(parts[0]);
      try: val=float(parts[1])
      except Exception: continue
      if n>1 and n==int(n): ap[n]=val
  if not ap:
    # Fallback: treat row index as n
    for i,line in enumerate(rows[1:], start=1):
      parts=[x.strip() for x in line.split(",")]
      if len(parts)>=2:
        try: ap[i]=float(parts[1])
        except Exception: pass
  if ap: sources.append(str(p))
  return ap,sources
def recover_from_p2(ap:Dict[int,float], meta, limit:int=5000)->Tuple[Dict[int,float],List[str]]:
  # If a_{p^2} present but a_p missing, use a_{p^2} = a_p^2 - p^{k-1}
  k=meta.get("k",0); src=[]
  ps=primes_up_to(limit)
  for p in ps:
    if p not in ap and (p*p) in ap:
      rhs=ap[p*p]+(p**(k-1))
      if rhs>=0: ap[p]=float((rhs)**0.5); src.append(f"p2->p:{p}")
  return ap,src
def satake_from_ap(ap:Dict[int,float], meta)->Dict[int,Tuple[float,float]]:
  k=meta.get("k",0); sat={}
  for p,a in ap.items():
    c=(p**(k-1))
    disc=a*a-4*c
    if disc>=0: r=disc**0.5; sat[p]=((a+r)/2.0,(a-r)/2.0)
    else: r=complex(0.0,(-disc)**0.5); sat[p]=((a+r)/2.0,(a-r)/2.0)
  return sat
def canonical_write(path,str_obj):
  pathlib.Path(path).write_text(str_obj,encoding="utf-8")
def main():
  ap,meta,sources=harvest_from_json()
  ap_csv,src2=harvest_from_tau_csv(meta); ap.update({k:v for k,v in ap_csv.items() if k not in ap}); sources+=src2
  ap,src3=recover_from_p2(ap,meta,limit=10000); sources+=src3
  meta["sources"]=sources
  # Only keep primes
  ps=primes_up_to(max(ap.keys()) if ap else 0)
  ap_prime={int(p):float(ap[p]) for p in ps if p in ap}
  sat=satake_from_ap(ap_prime,meta)
  obj={"ap":ap_prime,"satake":{str(p):[float(sat[p][0].real if isinstance(sat[p][0],complex) else sat[p][0]),float(sat[p][1].real if isinstance(sat[p][1],complex) else sat[p][1])] for p in sat}, "meta":meta, "provenance":{}}
  txt=json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n"
  canonical_write(AP_OUT, json.dumps({"ap":ap_prime,"provenance":{}},sort_keys=True,separators=(",",":"))+"\\n")
  canonical_write(SA_OUT, json.dumps({"satake":{str(k):v for k,v in obj["satake"].items()},"provenance":{}},sort_keys=True,separators=(",",":"))+"\\n")
  # combined file for validation
  pathlib.Path(".tau_ledger/langlands/combined_ap_satake.json").write_text(txt,encoding="utf-8")
  print(".tau_ledger/langlands/combined_ap_satake.json")
if __name__=="__main__": main()
