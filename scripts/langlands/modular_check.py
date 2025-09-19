import sys, os, re, math
n=int(sys.argv[1]); A=sys.argv[2]; B=sys.argv[3]; tol=float(sys.argv[4]) if len(sys.argv)>4 else 1e-3
floats=re.compile(rb"[0-9]+(?:\.[0-9]+)?")
def hecke_mean(root):
  total=0.0; count=0
  for dp,_,fs in os.walk(root):
    for fn in fs:
      if not fn.endswith(".json"): continue
      p=os.path.join(dp,fn)
      try: data=open(p,"rb").read()
      except: continue
      vals=[float(x) for x in floats.findall(data)]
      if not vals: continue
      m=max(vals) or 1.0
      for v in vals:
        x=min(1.0,max(1e-12,v/m))
        s=0.0
        for k in range(1,n+1): s+= x**(k/float(n))
        total += s/n; count += 1
  return (total/count) if count else 0.0
a=hecke_mean(A); b=hecke_mean(B); d=abs(a-b)
print(f"Delta={d:.6e}\ta={a:.12f}\tb={b:.12f}")
sys.exit(0 if d<tol else 1)
