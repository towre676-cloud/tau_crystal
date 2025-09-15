import io,json,math,sys,cmath
csv_path=".tau_ledger/seq/tau.csv"; out=".tau_ledger/experimental/bsd_rank1.json"
def dft(x):
  N=len(x); X=[0j]*N
  for k in range(N):
    s=0j; for n in range(N): s+=x[n]*cmath.exp(-2j*math.pi*k*n/N); X[k]=s
  return X
def idft(X):
  N=len(X); x=[0j]*N
  for n in range(N):
    s=0j; for k in range(N): s+=X[k]*cmath.exp(2j*math.pi*k*n/N); x[n]=s/N
  return x
def spectral_derivatives(y):
  N=len(y); Y=dft([complex(v,0.0) for v in y])
  # angular freqs for unit grid
  w=[2*math.pi*k/N for k in range(N)]
  Y1=[1j*w[k]*Y[k] for k in range(N)]
  Y2=[-(w[k]**2)*Y[k] for k in range(N)]
  f = idft(Y); f1=idft(Y1); f2=idft(Y2)
  return f,f1,f2
try: lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError:
  io.open(out,"w",encoding="utf-8").write("{\"rank1_candidates\":[]}\\n"); print(out); sys.exit(0)
ys=[]
for i,l in enumerate(lines):
  if i==0: continue
  parts=l.split(",");
  if len(parts)>=2:
    try: ys.append(float(parts[1]))
    except: pass
N=len(ys)
if N<8:
  io.open(out,"w",encoding="utf-8").write("{\"rank1_candidates\":[]}\\n"); print(out); sys.exit(0)
# zero-pad to power of two for nicer spectra (still DFT naive, but improves m index)
M=1
while M<N: M<<=1
ys2=ys+[ys[-1]]*(M-N)
f,f1,f2=spectral_derivatives(ys2)
m=M//2
mean=float(f[m].real); d1=float(f1[m].real); d2=float(f2[m].real)
flag=1 if (mean*mean<1e-8 and d1*d1>1e-8 and d2*d2<1e-8) else 0
obj={"rank1_candidates":[{"mean":mean,"d1":d1,"d2":d2,"rank1_flag":flag,"method":"spectral-fft"}]}
import os; os.makedirs(".tau_ledger/experimental",exist_ok=True)
io.open(out,"w",encoding="utf-8").write(json.dumps(obj,ensure_ascii=False,indent=2)+"\\n")
print(out)
