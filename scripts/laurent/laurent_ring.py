#!/usr/bin/env python3
import sys, csv, json, math
from collections import defaultdict
try:
    import numpy as np
except Exception as e:
    print(json.dumps({"error":"numpy-required","detail":str(e)})); sys.exit(0)

def _load_csv(path):
    rows=[]
    with open(path, newline='', encoding='utf-8') as f:
        rd=csv.reader(f)
        for r in rd:
            if not r or r[0].lstrip().startswith('#'): continue
            try:
                rr=float(r[0]); th=float(r[1]); re=float(r[2]); im=float(r[3])
                rows.append((rr, th, re+1j*im))
            except: pass
    if not rows: raise ValueError("no data")
    rows.sort(key=lambda t:(t[0],t[1]))
    return rows

def _group(rows):
    rings=defaultdict(list); ang=defaultdict(list)
    for rr,th,z in rows:
        rings[rr].append(z); ang[rr].append(th)
    R=[]
    for rr in sorted(rings):
        idx=np.argsort(ang[rr])
        zs=np.array(rings[rr],dtype=np.complex128)[idx]
        th=np.array(ang[rr],dtype=np.float64)[idx]
        R.append((float(rr),th,zs))
    return R

def _uniform(th):
    m=len(th); d=np.diff(np.r_[th, th[0]+2*np.pi])
    return np.allclose(d,(2*np.pi)/m,rtol=5e-4,atol=1e-6)

def _fft(z): return np.fft.fft(z)/len(z)

def _map_idx(M):
    idx=np.arange(M); idx[idx> M//2]-=M; return idx

def _collect(radii, F, nmax):
    K,M=F.shape
    nmap=_map_idx(M); col_of={}
    for c,n in enumerate(nmap):
        col_of.setdefault(n,c)
    coeffs=[]; a_mean={}; a_se_abs={}
    for n in range(-nmax,nmax+1):
        if n not in col_of: continue
        col=col_of[n]; c_n=F[:,col]
        with np.errstate(divide='ignore', invalid='ignore'):
            rpow=radii**n
            a_est=c_n/rpow
        a_mu=np.nanmean(a_est)
        a_mean[n]=a_mu
        if K>1:
            se=np.nanstd(np.abs(a_est),ddof=1)/np.sqrt(K)
        else:
            se=float('inf')
        a_se_abs[n]=float(se)
        rms=float(np.sqrt(np.nanmean(np.abs(a_est-a_mu)**2)))
        coeffs.append({"n":int(n),"real":float(a_mu.real),"imag":float(a_mu.imag),
                       "abs":float(abs(a_mu)),"se_real":0.0,"se_imag":0.0,
                       "se_abs":float(se),"rms_inconsistency":rms})
    return coeffs,a_mean,a_se_abs

def _energy(a_mean, r, nmax):
    return float(sum((abs(a_mean.get(n,0.0))**2)*(r**(2*n)) for n in range(-nmax,nmax+1)))

def compute(csv_path, conf=0.95, nmax=64):
    rows=_load_csv(csv_path)
    rings=_group(rows)
    filt=[]
    for r,th,zs in rings:
        if len(zs)>=8 and _uniform(th): filt.append((r,th,zs))
    if not filt: return {"error":"no-valid-rings"}
    radii=np.array([r for r,_,_ in filt],dtype=np.float64)
    F=np.vstack([_fft(z) for _,_,z in filt])
    K,M=F.shape
    if nmax> M//2: nmax=M//2
    coeffs,a_mean,a_se=_collect(radii,F,nmax)
    rmin=float(np.min(radii)); rmax=float(np.max(radii))
    rstar=math.sqrt(rmin*rmax); E_rstar=_energy(a_mean,rstar,nmax)
    # pole order via simple threshold
    ztab={0.80:1.281551565545,0.90:1.644853626951,0.95:1.959963984540,0.98:2.326347874041,0.99:2.575829303549}
    zval=ztab[min(ztab.keys(), key=lambda x:abs(x-conf))]
    sig=[]
    for n in range(-nmax,0):
        mu=a_mean.get(n,0.0); thr=zval*max(a_se.get(n,0.0),0.0)+1e-12
        if abs(mu)>thr: sig.append(-n)
    nu=int(max(sig) if sig else 0)
    a_m1=a_mean.get(-1,0.0+0.0j)
    R_sq=sum((abs(a_mean.get(n,0.0))**2)*(rstar**(2*n)) for n in range(-nmax,0))
    D_sq=sum((abs(a_mean.get(n,0.0))**2)*(rstar**(2*n)) for n in range(0,nmax+1))
    Ener=[_energy(a_mean,float(r),nmax) for r in radii]
    dlog=[float(-(math.log(Ener[i])-math.log(Ener[i-1]))) if Ener[i]>0 and Ener[i-1]>0 else 0.0
          for i in range(1,len(Ener))]
    return {
      "coefficients": coeffs,
      "summary": {
        "kappa_A": float((math.log(rmax/rmin))/(2.0*math.pi)),
        "nu": int(nu),
        "residue_a_minus_1": {"real": float(a_m1.real), "imag": float(a_m1.imag), "abs": float(abs(a_m1))},
        "norm_R": float(math.sqrt(R_sq)),
        "norm_D": float(math.sqrt(D_sq)),
        "E_rstar": float(E_rstar),
        "r_star": float(rstar),
        "r_min": float(rmin),
        "r_max": float(rmax),
        "conf": float(conf)
      },
      "tau_series": { "radii":[float(x) for x in radii],
                      "energy_per_ring":[float(x) for x in Ener],
                      "delta_tau": dlog },
      "meta": {"version":1.0,"M":float(M),"K":float(K),"nmax":float(nmax)}
    }

if __name__=="__main__":
    if len(sys.argv)<2:
        print(json.dumps({"error":"usage","hint":"laurent_ring.py RING_CSV [nmax] [conf]"})); sys.exit(0)
    csv_path=sys.argv[1]
    nmax=int(sys.argv[2]) if len(sys.argv)>2 else 64
    conf=float(sys.argv[3]) if len(sys.argv)>3 else 0.95
    try:
        out=compute(csv_path,conf=conf,nmax=nmax)
    except Exception as e:
        print(json.dumps({"error":"compute-failed","detail":str(e)})); sys.exit(0)
    print(json.dumps(out,ensure_ascii=False,indent=2))
