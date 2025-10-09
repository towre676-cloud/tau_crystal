import cmath, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier_fix import cubic_coeff_C
EPS=1e-18
def Ell(tau,x,N): return -600.0*cubic_coeff_C(x,tau,N,1e-5)
tau1=0.12+9.0j; tau2=0.19+8.0j; x=0.27; N=160
q1=cmath.exp(2j*cmath.pi*tau1); q2=cmath.exp(2j*cmath.pi*tau2)
v1=Ell(tau1,x,N); v2=Ell(tau2,x,N)
den=q1-q2
a1=(v1-v2)/den if abs(den)>EPS else complex('nan')
a0=v1-a1*q1 if isinstance(a1,complex) else complex('nan')
y=cmath.exp(2j*cmath.pi*x); chiy=-1.0/y+101.0
rel=(abs(a0-chiy)/(abs(chiy) if abs(chiy)>EPS else 1.0)) if isinstance(a0,complex) else float('nan')
with open('tsv/elliptic_q0_q1_pair.tsv','w') as f:
    f.write('ReTau1\tImTau1\tReTau2\tImTau2\tx\tN\tRe_a0\tIm_a0\tRe_chiy\tIm_chiy\tRelErr_q0\tRe_a1\tIm_a1\n')
with open('tsv/elliptic_q0_q1_pair.tsv','a') as f:
    f.write(f"{tau1.real}\t{tau1.imag}\t{tau2.real}\t{tau2.imag}\t{x}\t{N}\t{a0.real if isinstance(a0,complex) else float('nan')}\t{a0.imag if isinstance(a0,complex) else float('nan')}\t{chiy.real}\t{chiy.imag}\t{rel}\t{a1.real if isinstance(a1,complex) else float('nan')}\t{a1.imag if isinstance(a1,complex) else float('nan')}\n")
