import cmath, sys
from ell_fourier import phi_third_at_zero
def main():
    Ns=[80,120]
    taus=[0.1+1.0j, 0.1+2.0j, 0.0+3.0j]
    xs=[0.1, 0.2]
    out='tsv/elliptic_C_derivatives.tsv'
    with open(out,'w',newline='') as f:
        f.write('ReTau\tImTau\tX\tN\tReC3\tImC3\n')
        for N in Ns:
            for tau in taus:
                for x in xs:
                    val = phi_third_at_zero(x,tau,N)
                    if val is None: continue
                    f.write(f"{tau.real}\t{tau.imag}\t{x}\t{N}\t{val.real}\t{val.imag}\n")
if __name__=='__main__': main()
