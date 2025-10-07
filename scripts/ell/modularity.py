## [CY3 Normal Form]
## Ell_X(q,y) = (chi(X)/2) * phi_{0,3/2}(q,y)   (weight 0, index 3/2)
## Quintic: chi = -200 -> Ell = -100 * phi_{0,3/2}
## Dictionary:
##   C := (1/6) * d^3/dz^3 Phi |_{z=0},   phi_{0,3/2} = C/6
##   cubic factor = geometric: with c1=0, cubic symmetric polynomial = 3*c3(TX)
## Holomorphy: theta-ratio poles cancel over three Chern roots (CY3), giving a holomorphic weak Jacobi form.
import cmath, math, os, sys
m=1.5  # Jacobi index (quintic)
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier import theta1_and_derivs
EPS = 1e-18
def proxy_ell(tau,z,N):
    t0,t1,_,_ = theta1_and_derivs(0,tau,N)
    a0,_,_,_  = theta1_and_derivs(z,tau,N)
    if abs(a0) < EPS: raise ZeroDivisionError('theta1(z) ≈ 0; near lattice hit')
    return t1/a0
def relerr(a,b):
    den = abs(b) if abs(b)>EPS else 1.0
    return abs(a-b)/den
def safe_row(fh, case, tau, z, N, lhs, rhs, note=''):
    fh.write(f"{case}\t{tau.real}\t{tau.imag}\t{z}\t{N}\t{lhs.real if isinstance(lhs,complex) else float('nan')}\t{rhs.real if isinstance(rhs,complex) else float('nan')}\t{relerr(lhs,rhs) if isinstance(lhs,complex) and isinstance(rhs,complex) else float('nan')}\t{note}\n")
def main():
    out='tsv/elliptic_modularity_checks.tsv'
    with open(out,'w') as f:
        f.write('case\tReTau\tImTau\tz\tN\tLHS_re\tRHS_re\tRelErr\tNote\n')
        for N in (80,120,160):
            for tau in (0.11+8.0j, 0.07+6.5j):
                for z in (0.37, 0.52, 0.413):
                    try:
                        lhs = proxy_ell(tau+1,z,N)
                        rhs = proxy_ell(tau,z,N)
                        safe_row(f,'tau+1',tau,z,N,lhs,rhs,'')
                    except Exception as e:
                        safe_row(f,'tau+1',tau,z,N,complex('nan'),complex('nan'),str(e))
                    try:
                        tauS = -1.0/tau
                        zS   = z/tau
                        lhsS = proxy_ell(tauS,zS,N)
                        rhsS = proxy_ell(tau,z,N)
                        safe_row(f,'S',tau,z,N,lhsS, rhsS, '')
                    except Exception as e:
                        safe_row(f,'S',tau,z,N,complex('nan'),complex('nan'),str(e))
                    try:
                        lhs1 = proxy_ell(tau,z+1,N)
                        rhs1 = proxy_ell(tau,z,N)
                        safe_row(f,'z+1',tau,z,N,lhs1, rhs1, '')
                    except Exception as e:
                        safe_row(f,'z+1',tau,z,N,complex('nan'),complex('nan'),str(e))
                    try:
                        lhst = proxy_ell(tau,z+tau,N)
                        rhst = proxy_ell(tau,z,N)
                        safe_row(f,'z+tau',tau,z,N,lhst, rhst, '')
                    except Exception as e:
                        safe_row(f,'z+tau',tau,z,N,complex('nan'),complex('nan'),str(e))
if __name__=='__main__': main()
