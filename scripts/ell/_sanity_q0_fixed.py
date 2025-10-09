import os, sys, cmath
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier_fix import cubic_coeff_C
tau = 0.12+9.0j; x = 0.27; N = 120
C = cubic_coeff_C(x,tau,N,1e-5)
Ell = -600.0*C
open('tsv/elliptic_q_sanity.tsv','w').write('ReTau\tImTau\tx\tN\tReEll\tImEll\n')
open('tsv/elliptic_q_sanity.tsv','a').write(f"{tau.real}\t{tau.imag}\t{x}\t{N}\t{Ell.real}\t{Ell.imag}\n")
