import mpmath as mp

def L_GL2_from_ap(ap: dict[int,float], k:int, N:int, prime_list=None):
    """Return L(s) via Euler product over available primes (from ap keys if present)."""
    if prime_list is None: prime_list = sorted(ap.keys())
    # Recover Satake from ap when needed (holomorphic normalization)
    def satake_from_ap(a,p):
        # x^2 - a x + p^{k-1} = 0  (trivial nebentypus)
        c = p**(k-1)
        disc = a*a - 4*c
        if disc >= 0:
            r = mp.sqrt(disc); return ( (a+r)/2, (a-r)/2 )
        else:
            r = 1j*mp.sqrt(-disc); return ( (a+r)/2, (a-r)/2 )
    def L(s):
        acc = mp.mpf("1.0")
        for p in prime_list:
            a = ap.get(p, None)
            if a is None: continue
            alpha,beta = satake_from_ap(a,p)
            acc *= 1/((1 - alpha* p**(-s))*(1 - beta* p**(-s)))
        return acc
    return L

def L_Sym2_from_satake(sat: dict[int,tuple], prime_list=None):
    """Sym^2 local factors: (1 - α^2 p^{-s})^{-1} (1 - αβ p^{-s})^{-1} (1 - β^2 p^{-s})^{-1}."""
    if prime_list is None: prime_list = sorted(sat.keys())
    def L(s):
        acc = mp.mpf("1.0")
        for p in prime_list:
            ab = sat.get(p, None)
            if ab is None: continue
            a,b = complex(ab[0]), complex(ab[1])
            acc *= 1/((1 - (a*a)*p**(-s))*(1 - (a*b)*p**(-s))*(1 - (b*b)*p**(-s)))
        return acc
    return L
