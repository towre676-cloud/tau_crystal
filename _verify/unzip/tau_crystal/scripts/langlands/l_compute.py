import sys, os, re, math
s=float(sys.argv[1]) if len(sys.argv)>1 else 1.0
root=sys.argv[2] if len(sys.argv)>2 else ".tau_ledger"
floats=re.compile(rb"[0-9]+(?:\.[0-9]+)?")
prod=1.0; count=0
for dp,_,fs in os.walk(root):
  for fn in fs:
    if not fn.endswith(".json"): continue
    p=os.path.join(dp,fn)
    try: data=open(p,"rb").read()
    except: continue
    vals=[float(x) for x in floats.findall(data)]
    if not vals: continue
    m=max(vals) or 1.0
    seq=[min(1.0, max(1e-12, v/m)) for v in vals]
    ms=sum(seq)/len(seq)
    den=max(1.0, float(len(seq)))*(1.0+0.5*(s-1.0))
    ratio=ms/den
    if ratio>=0.999999: ratio=0.999999
    prod*=1.0/(1.0 - ratio); count+=1
if count==0: print("1.000000000000\t0")
else: print(f"{prod:.12f}\t{count}")
