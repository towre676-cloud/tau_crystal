import io,json,math,os,sys
import numpy as np
from numpy.fft import fft,ifft
csv_path=".tau_ledger/seq/tau.csv"; out=".tau_ledger/experimental/fft_bsd.json"
os.makedirs(os.path.dirname(out),exist_ok=True)
try:
  lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError:
  json.dump({"fft_bsd":{}},io.open(out,"w",encoding="utf-8")); print(out); sys.exit(0)
ys=[float(l.split(",")[1]) for i,l in enumerate(lines) if i>0 and len(l.split(","))>=2]
n=len(ys)
if n<8:
  json.dump({"fft_bsd":{}},io.open(out,"w",encoding="utf-8")); print(out); sys.exit(0)
hann=np.hanning(n)
z=np.asarray(ys)*hann
pad=1<<(n.bit_length())
z=np.pad(z,(0,pad-n))
fz=fft(z)
k=np.fft.fftfreq(pad,1.0/pad)
dfz=1j*2*np.pi*k*fz; dz=ifft(dfz).real
d2fz=(1j*2*np.pi*k)**2*fz; d2z=ifft(d2fz).real
idx=n//2
d1=float(dz[idx]); d2=float(d2z[idx])
rank1=bool(abs(d1)>1e-6 and abs(d2)<1e-6)
obj={"rank1_flag":rank1,"d1_analytic":d1,"d2_analytic":d2,"hann_window":True,"zero_pad":int(pad),"freq_resolution":float(1.0/pad)}
json.dump({"fft_bsd":obj},io.open(out,"w",encoding="utf-8"),indent=2); print(out)
