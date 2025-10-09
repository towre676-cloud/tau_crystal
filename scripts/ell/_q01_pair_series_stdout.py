import cmath, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
from ell_series import C_series
ABS_EPS=1e-12
def Ell(tau,x,N): return -600.0*C_series(x,tau,N)
def ffmt(x):
    try: return f"{float(x):.16g}"
    except Exception: return 'NaN'
def main():
    tau1=0.10+3.0j; tau2=0.17+2.6j; x=0.25; N=240
    q1=cmath.exp(2j*cmath.pi*tau1); q2=cmath.exp(2j*cmath.pi*tau2)
    v1=Ell(tau1,x,N); v2=Ell(tau2,x,N)
    y=cmath.exp(2j*cmath.pi*x); chiy=-1.0/y+101.0
    den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
    a0=a1=None
    if abs(den) > ABS_EPS*scale:
        a1=(v1-v2)/den; a0=v1 - a1*q1
    hdr=['ReTau1','ImTau1','ReTau2','ImTau2','x','N','abs_q1','abs_q2','Re_a0','Im_a0','Re_chiy','Im_chiy','RelErr_q0','Re_a1','Im_a1']
    rel=(abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS_EPS else 1.0)) if a0 is not None else float('nan')
    row=[ffmt(tau1.real),ffmt(tau1.imag),ffmt(tau2.real),ffmt(tau2.imag),ffmt(x),str(N),ffmt(abs(q1)),ffmt(abs(q2)),
         (ffmt(a0.real) if a0 is not None else 'NaN'),(ffmt(a0.imag) if a0 is not None else 'NaN'),
         ffmt(chiy.real), ffmt(chiy.imag), ffmt(rel),
         (ffmt(a1.real) if a1 is not None else 'NaN'),(ffmt(a1.imag) if a1 is not None else 'NaN')]
    print('\t'.join(hdr))
    print('\t'.join(row))
if __name__=='__main__': main()
