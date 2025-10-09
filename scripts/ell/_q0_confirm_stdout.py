import cmath, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
from ell_series import C_series
ABS_EPS=1e-12
def Ell(tau,x,N): return -600.0*C_series(x,tau,N)
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def main():
    tau1=0.10+3.0j; tau2=0.17+2.6j; x=0.25; N=240
    q1=cmath.exp(2j*cmath.pi*tau1); q2=cmath.exp(2j*cmath.pi*tau2)
    v1=Ell(tau1,x,N); v2=Ell(tau2,x,N)
    den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
    a0=a1=None
    if abs(den)>ABS_EPS*scale:\n        a1=(v1-v2)/den; a0=v1-a1*q1
    y=cmath.exp(2j*cmath.pi*x); chiy=-1.0/y+101.0
    rel=(abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS_EPS else 1.0)) if a0 is not None else float('nan')
    print('x=',f(x))
    print('y =',f(y.real),'+',f(y.imag),'i')
    print('a0=',f(a0.real),'+',f(a0.imag),'i')
    print('chi_y=',f(chiy.real),'+',f(chiy.imag),'i')
    print('RelErr_q0=',f(rel))
if __name__=='__main__': main()
