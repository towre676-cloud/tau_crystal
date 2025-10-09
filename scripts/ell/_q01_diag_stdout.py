import cmath, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
from ell_series import C_series
ABS_EPS=1e-12
def Ell(tau,x,N): return -600.0*C_series(x,tau,N)
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def solve_pair(x,N,tau1,tau2):
    q1=cmath.exp(2j*cmath.pi*tau1); q2=cmath.exp(2j*cmath.pi*tau2)
    v1=Ell(tau1,x,N); v2=Ell(tau2,x,N)
    den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
    if abs(den)<=ABS_EPS*scale: return None,None
    a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1
def main():
    tau1=0.10+3.0j; tau2=0.17+2.6j; N=240
    xs=[0.22,0.25,0.28,0.30]
    print('\t'.join(['x','y.re','y.im','chi_y.re','chi_y.im','a0.re','a0.im','relerr']))
    for x in xs:
        y=cmath.exp(2j*cmath.pi*x); chiy=-1.0/y+101.0
        a0,a1=solve_pair(x,N,tau1,tau2)
        if a0 is None:\n            print('\t'.join([f(x),f(y.real),f(y.imag),f(chiy.real),f(chiy.imag),'NaN','NaN','NaN']))\n            continue
        rel=abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS_EPS else 1.0)
        print('\t'.join([f(x),f(y.real),f(y.imag),f(chiy.real),f(chiy.imag),f(a0.real),f(a0.imag),f(rel)]))
if __name__=='__main__': main()
