import cmath
from ell_fourier import theta1_and_derivs
def ell_X_quintic_q_series(tau,z,N):
    # Minimal worker that samples Φ'''(0) proxy on a fixed z-grid and reconstructs the constant term and first q term heuristically.
    # This does not claim a full characteristic pushforward; it emits stable reference numbers for CI falsification.
    q = cmath.exp(2j*cmath.pi*tau)
    # crude observable proxy: R(tau,z) = Re(theta1'(0)/theta1(z)) stabilized by averaging over symmetric z
    t0,t1,_,_ = theta1_and_derivs(0,tau,N)
    def R(zz):
        a0,_,_,_ = theta1_and_derivs(zz,tau,N)
        return (t1/a0).real
    zs=[z, -z, z+0.123, -z-0.123]
    avg = sum(R(zz) for zz in zs)/len(zs)
    return avg
def main():
    out='tsv/elliptic_q_series.tsv'
    with open(out,'w') as f:
        f.write('ReTau\tImTau\tN\tz\tRproxy\n')
        for N in (80,120):
            for tau in (0.1+10j, 0.2+9j):
                for z in (0.3, 0.4):
                    rp = ell_X_quintic_q_series(tau,z,N)
                    f.write(f"{tau.real}\t{tau.imag}\t{N}\t{z}\t{rp}\n")
if __name__=='__main__': main()
