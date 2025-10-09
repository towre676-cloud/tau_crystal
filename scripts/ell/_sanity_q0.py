import cmath, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier import phi_third_at_zero
tau=0.12+9.0j; z=0.23; N=120
val = phi_third_at_zero(z,tau,N)
if val is None: raise SystemExit(2)
Ell = -600.0*val
open('tsv/elliptic_q_sanity.tsv','w').write('ReTau\tImTau\tz\tN\tReEll\tImEll\n')
open('tsv/elliptic_q_sanity.tsv','a').write(f"{tau.real}\t{tau.imag}\t{z}\t{N}\t{Ell.real}\t{Ell.imag}\n")
