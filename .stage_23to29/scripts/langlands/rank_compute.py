import sys, os, re
root=sys.argv[1] if len(sys.argv)>1 else ".tau_ledger"
floats=re.compile(rb"[0-9]+(?:\.[0-9]+)?")
def L_of_s(s):
  import math
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
  return prod, count
f1,c1=L_of_s(1.0)
if c1==0: print(0); raise SystemExit
f2,_=L_of_s(1.05); f0,_=L_of_s(0.95)
eps=0.05; der=(f2-f0)/(2.0*eps)
rank = 1 if abs(f1)<1e-6 and abs(der)>1e-6 else (2 if abs(f1)<1e-6 and abs(der)<1e-6 else 0)
print(rank)
