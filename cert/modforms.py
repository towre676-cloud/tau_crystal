from mpmath import mp, exp, pi

def _sigma_s_sieve(N, s):
    sig=[mp.mpf('0')]*(N+1)
    for d in range(1,N+1):
        ds = mp.mpf(d)**s
        for m in range(d, N+1, d):
            sig[m] += ds
    return sig

def e_series_coeffs(N):
    s1=_sigma_s_sieve(N,1); s3=_sigma_s_sieve(N,3); s5=_sigma_s_sieve(N,5)
    a2=[mp.mpf('0')]*(N+1); a4=[mp.mpf('0')]*(N+1); a6=[mp.mpf('0')]*(N+1)
    a2[0]=mp.mpf('1'); a4[0]=mp.mpf('1'); a6[0]=mp.mpf('1')
    for n in range(1,N+1):
        a2[n] = -24*s1[n]; a4[n] = 240*s3[n]; a6[n] = -504*s5[n]
    return a2,a4,a6

def eval_series(a, q):
    s = mp.mpf('0'); qn = mp.mpf('1')
    for c in a:
        s += c*qn
        qn *= q
    return s

def D_eval(a, q):
    s = mp.mpf('0'); qn = mp.mpf('1')
    for n,c in enumerate(a):
        s += (n*c)*qn
        qn *= q
    return s

def choose_N_for_tol(q_abs, digits):
    if q_abs >= mp.mpf('0.9'):
        raise ValueError('q too large; increase Im(tau)')
    # crude bound: pick N so that |q|^(N+1)/(1-|q|) < 10^{-digits}/100
    target = digits*mp.log(10) + mp.log(100)
    N = int(mp.ceil(target/(-mp.log(q_abs)+mp.mpf('1e-30'))))
    return max(N, 50)
