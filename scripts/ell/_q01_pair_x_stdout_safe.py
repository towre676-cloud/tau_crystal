import os, sys, cmath, math, traceback
sys.path.insert(0, os.path.join(os.getcwd(),'scripts','ell'))
ABS=1e-12
def f(x):
    try: return f"{float(x):.12g}"
    except: return 'NaN'
def ascii_only(s): return (str(s).encode('ascii','ignore')).decode('ascii')
print('\t'.join(['z','y.re','y.im','a0.re','a0.im','chi_y.re','chi_y.im','rel','Note']))
try:
    from ell_series_x import Cx_series
except Exception as e:
    note = 'IMPORT_FAIL:' + ascii_only(e)
    for z in [0.22,0.25,0.28]:
        y=cmath.exp(2j*cmath.pi*z); chiy=-1.0/y+101.0
        print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chiy.real),f(chiy.imag),'NaN',note]))
    raise SystemExit(0)
def Ell(tau,z,N): return -600.0*Cx_series(z,tau,N)
def solve_a0a1(z,N,t1,t2):
    try:
        q1=cmath.exp(2j*cmath.pi*t1); q2=cmath.exp(2j*cmath.pi*t2)
        v1=Ell(t1,z,N); v2=Ell(t2,z,N)
        den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
        if abs(den)<=ABS*scale: return None,None,'den~0'
        a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1,''
    except Exception as e:
        return None,None,ascii_only(e)
try:
    N=320; t1=0.12+3.4j; t2=0.19+2.7j; zs=[0.22,0.25,0.28]
    for z in zs:
        y=cmath.exp(2j*cmath.pi*z); chiy=-1.0/y+101.0
        a0,a1,note = solve_a0a1(z,N,t1,t2)
        if a0 is None:
            print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chiy.real),f(chiy.imag),'NaN',ascii_only(note)]))
            continue
        rel = abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS else 1.0)
        print('\t'.join([f(z),f(y.real),f(y.imag),f(a0.real),f(a0.imag),f(chiy.real),f(chiy.imag),f(rel),ascii_only(note)]))
except Exception as e:
    tb = ascii_only(''.join(traceback.format_exc()).splitlines()[-1])
    for z in [0.22,0.25,0.28]:
        y=cmath.exp(2j*cmath.pi*z); chiy=-1.0/y+101.0
        print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chiy.real),f(chiy.imag),'NaN','TOPLEVEL:'+tb]))
