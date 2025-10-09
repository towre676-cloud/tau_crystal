import cmath, math, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier import phi_third_at_zero
EPS=1e-18
def ell_quintic_value(tau,z,N):
    val = phi_third_at_zero(z,tau,N)
    if val is None: raise ValueError('C(=Phi'''(0)/6) unavailable on special-branch; choose different z or increase N')
    return -600.0*val
def solve_a0_a1(v1,v2,q1,q2):
    # Solve v ≈ a0 + a1 q at two small-q points
    den = (q1 - q2)
    if abs(den) < EPS: raise ZeroDivisionError('q1≈q2; pick distinct taus')
    a1 = (v1 - v2)/den
    a0 = v1 - a1*q1
    return a0, a1
def chi_y_target(y):
    # User-stated checkpoint: chi_y = -y^{-1} + 101
    return -1.0/(y) + 101.0
def main():
    out='tsv/elliptic_q0_q1_pushforward.tsv'
    with open(out,'w') as f:
        f.write('ReTau1\tImTau1\tReTau2\tImTau2\tN\tz\ty\tRe_a0\tIm_a0\tRe_chiy\tIm_chiy\tRelErr_q0\tRe_a1\tIm_a1\n')
        Ns=(120,160)
        taus=[(0.10,10.0),(0.18,9.0)]  # two distinct small-q points
        zgrid=(0.21, 0.33, 0.41)       # avoid theta lattice hits
        for N in Ns:
            (r1,i1),(r2,i2)=taus
            tau1 = complex(r1,i1); tau2 = complex(r2,i2)
            q1 = cmath.exp(2j*cmath.pi*tau1)
            q2 = cmath.exp(2j*cmath.pi*tau2)
            for z in zgrid:
                try:
                    v1 = ell_quintic_value(tau1,z,N)
                    v2 = ell_quintic_value(tau2,z,N)
                    a0,a1 = solve_a0_a1(v1,v2,q1,q2)
                    # Evaluate target chi_y at the same y = e^{2π i z}
                    y = cmath.exp(2j*cmath.pi*z)
                    chiy = chi_y_target(y)
                    num = abs(a0 - chiy)
                    den = abs(chiy) if abs(chiy)>EPS else 1.0
                    rel = num/den
                    f.write(f"{r1}\t{i1}\t{r2}\t{i2}\t{N}\t{z}\t{y}\t{a0.real}\t{a0.imag}\t{chiy.real}\t{chiy.imag}\t{rel}\t{a1.real}\t{a1.imag}\n")
                except Exception as e:
                    # Emit NaNs for traceability when special cases occur
                    y = cmath.exp(2j*cmath.pi*z)
                    f.write(f"{r1}\t{i1}\t{r2}\t{i2}\t{N}\t{z}\t{y}\tNaN\tNaN\tNaN\tNaN\tNaN\tNaN\tNaN\n")
if __name__=='__main__': main()
