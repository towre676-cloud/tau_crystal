import io, json, math, sys
tau_csv=".tau_ledger/seq/tau.csv"
out_path=".tau_ledger/automorphic/critical_zeros.json"
try:
  lines=io.open(tau_csv,"r",encoding="utf-8").read().strip().splitlines()
  xs=[]
  for i,l in enumerate(lines):
    if i==0: continue
    parts=l.split(",");
    if len(parts)>=2:
      try: xs.append(float(parts[1]))
      except: pass
except FileNotFoundError:
  io.open(out_path,"w",encoding="utf-8").write("{\"critical_zeros\":[]}\n"); print(out_path); sys.exit(0)
if not xs:
  io.open(out_path,"w",encoding="utf-8").write("{\"critical_zeros\":[]}\n"); print(out_path); sys.exit(0)
# Empirical Dirichlet series L(s)=sum_{n<=N} x_n / n^s
N=len(xs)
grid_re=[i/10.0 for i in range(1,10)]  # 0.1..0.9
grid_im=[0.0]+[i/10.0 for i in range(2,21,2)]+[-i/10.0 for i in range(2,21,2)]
zeros=[]
for sr in grid_re:
  for si in grid_im:
    re=0.0; im=0.0
    for n,x in enumerate(xs, start=1):
      a = n**(-sr); ang = -si*math.log(n)
      re += x * a * math.cos(ang)
      im += x * a * math.sin(ang)
    mag2 = re*re + im*im
    if mag2 < 1e-8:
      zeros.append({"re":sr,"im":si,"L_re":re,"L_im":im})
io.open(out_path,"w",encoding="utf-8").write(json.dumps({"critical_zeros":zeros},ensure_ascii=False,indent=2)+"\n")
print(out_path)
