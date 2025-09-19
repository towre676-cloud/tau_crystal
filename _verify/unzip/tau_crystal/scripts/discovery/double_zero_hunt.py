import io,json,math,os,sys
import numpy as np
from numpy.fft import fft,ifft
csv_path=".tau_ledger/seq/tau.csv"
out=".tau_ledger/discovery/double_zero.json"
os.makedirs(os.path.dirname(out),exist_ok=True)
def write(obj): open(out,"w",encoding="utf-8").write(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n")
try:
  lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError:
  write({"double_zero":{"flag":False,"reason":"missing tau.csv"}}); print(out); sys.exit(0)
ys=[float(l.split(",")[1]) for i,l in enumerate(lines) if i>0 and len(l.split(","))>=2]
n=len(ys)
if n<16: write({"double_zero":{"flag":False,"reason":"insufficient samples","n":n}}); print(out); sys.exit(0)
# critical-line via FFT complex derivative (Hann + zero-pad)
hann=np.hanning(n); z=np.asarray(ys)*hann; pad=1<<(n.bit_length()); z=np.pad(z,(0,max(0,pad-n)))
fz=fft(z); k=np.fft.fftfreq(len(z),1.0/len(z))
dz=ifft(1j*2*np.pi*k*fz).real; d2z=ifft((1j*2*np.pi*k)**2*fz).real; idx=n//2
d1=float(dz[idx]); d2=float(d2z[idx])
crit_zeros=[]
for im in np.arange(0,2.05,0.05):
  s=0.5+1j*float(im)
  denom=(1 - (d1/(s if s!=0 else 1e-18)))
  l_crit=1.0/denom if abs(denom)>1e-12 else 1e12
  if abs(l_crit)<1e-6: crit_zeros.append({"re":0.5,"im":float(im)})
# symmetric-square crude Euler product outside strip
primes=[2,3,5,7,11,13,17,19]
alpha={p:float(np.mean(ys)) for p in primes}
sym2_outside=[]
for re in np.arange(1.1,3.05,0.10):
  for im in np.arange(0,2.05,0.10):
    t=complex(float(re),float(im)); L=1.0
    for p in primes:
      denom=1.0 - (alpha[p]*alpha[p])*(p**(-t))
      if abs(denom)<1e-12: denom=1e-12
      L*=1.0/denom
    if abs(L)<1e-6: sym2_outside.append({"re":float(re),"im":float(im)})
flag = bool(crit_zeros and sym2_outside)
obj={"double_zero":{"flag":flag,"critical_zeros":crit_zeros,"sym2_outside_strip":sym2_outside,
     "d1":d1,"d2":d2,"hann":True,"zero_pad":int(len(z)),"freq_res":float(1.0/len(z)),"heuristic_primes":primes}}
write(obj); print(out)
