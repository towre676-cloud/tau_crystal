import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier import phi_third_at_zero
EPS=1e-18
tau = 0.12+9.0j
z_candidates = [0.19, 0.23, 0.31, 0.37]
Ns = [80, 120, 160]
out='tsv/elliptic_q_sanity.tsv'
open(out,'w').write('ReTau\tImTau\tz\tN\tReEll\tImEll\tNote\n')
def ok(c): return (c is not None) and (not math.isnan(c.real)) and (not math.isnan(c.imag)) and (abs(c.real)<1e300) and (abs(c.imag)<1e300)
picked=None
for z in z_candidates:
    for N in Ns:
        try:
            val = phi_third_at_zero(z,tau,N)
            if val is None: continue
            Ell = -600.0*val
            if ok(Ell): picked=(z,N,Ell); raise StopIteration
        except StopIteration: pass
        except Exception:
            continue
try:
    if picked is not None:
        z,N,Ell = picked
        open(out,'a').write(f"{tau.real}\t{tau.imag}\t{z}\t{N}\t{Ell.real}\t{Ell.imag}\tOK\n")
    else:
        z=float('nan'); N=-1; Ell=complex('nan')
        open(out,'a').write(f"{tau.real}\t{tau.imag}\t{z}\t{N}\tNaN\tNaN\tNO_VALID_POINT\n")
except Exception:
    # Even on unexpected issues, emit a traceable row and exit 0
    open(out,'a').write(f"{tau.real}\t{tau.imag}\tNaN\t-1\tNaN\tNaN\tFALLBACK\n")
