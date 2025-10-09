import cmath, os, sys, math
sys.path.insert(0, os.path.join(os.getcwd(),'scripts','ell'))
from ell_series_x import Cx_series
ABS=1e-12
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def Ell(tau,z,N): return -600.0*Cx_series(z,tau,N)
def solve_a0a1(z,N,t1,t2):
    q1=cmath.exp(2j*cmath.pi*t1); q2=cmath.exp(2j*cmath.pi*t2)
    v1=Ell(t1,z,N); v2=Ell(t2,z,N)
    den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
    if abs(den)<=ABS*scale: return None,None
    a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1
def main():
    N=240; t1=0.10+3.0j; t2=0.17+2.6j; zs=[0.22,0.25,0.28]
    print('\t'.join(['z','y.re','y.im','a0.re','a0.im','chi_y.re','chi_y.im','rel']))
    for z in zs:
        a0,a1=solve_a0a1(z,N,t1,t2)
        y=cmath.exp(2j*cmath.pi*z); chiy=-1.0/y+101.0
        if a0 is None:
            print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chiy.real),f(chiy.imag),'NaN']))
            continue
        rel=abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS else 1.0)
        print('\t'.join([f(z),f(y.real),f(y.imag),f(a0.real),f(a0.imag),f(chiy.real),f(chiy.imag),f(rel)]))
if __name__=='__main__': main()
