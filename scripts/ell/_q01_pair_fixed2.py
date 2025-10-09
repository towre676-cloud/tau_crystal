import cmath, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier_fix import cubic_coeff_C
EPS=1e-18
def safe_Ell(tau,x,N,h):
    try:
        v = cubic_coeff_C(x,tau,N,h)
        if v is None: return None, 'C=None'
        E = -600.0*v
        if not (math.isfinite(E.real) and math.isfinite(E.imag)): return None,'nonfinite Ell'
        return E, ''
    except Exception as e:
        return None, str(e)
def main():
    out='tsv/elliptic_q0_q1_pair.tsv'
    with open(out,'w') as f:
        f.write('ReTau1\tImTau1\tReTau2\tImTau2\tx\tN\th\tRe_a0\tIm_a0\tRe_chiy\tIm_chiy\tRelErr_q0\tRe_a1\tIm_a1\tNote\n')
    # wider Im(tau) gap for smaller |q|; avoid near-collision of q1,q2
    tau1=0.08+11.0j; tau2=0.17+9.5j
    x=0.27; N=200; h=5e-6
    q1=cmath.exp(2j*cmath.pi*tau1); q2=cmath.exp(2j*cmath.pi*tau2)
    v1,n1 = safe_Ell(tau1,x,N,h)
    v2,n2 = safe_Ell(tau2,x,N,h)
    y=cmath.exp(2j*cmath.pi*x); chiy = -1.0/y + 101.0
    note=';'.join([s for s in (n1,n2) if s])
    a0=a1=None
    if (v1 is not None) and (v2 is not None):
        den = q1 - q2
        if abs(den)>EPS:
            a1 = (v1 - v2)/den
            a0 = v1 - a1*q1
        else:
            note = (note+';den≈0').strip(';')
    def R(v):
        return abs(v - chiy)/(abs(chiy) if abs(chiy)>EPS else 1.0) if (v is not None) else float('nan')
    rel = R(a0)
    with open(out,'a') as f:
        f.write(f"{tau1.real}\t{tau1.imag}\t{tau2.real}\t{tau2.imag}\t{x}\t{N}\t{h}\t{(a0.real if a0 is not None else float('nan'))}\t{(a0.imag if a0 is not None else float('nan'))}\t{chiy.real}\t{chiy.imag}\t{rel}\t{(a1.real if a1 is not None else float('nan'))}\t{(a1.imag if a1 is not None else float('nan'))}\t{note}\n")
if __name__=='__main__': main()
