import cmath, math, traceback
from ell_theta_cubic import C_x
ABS=1e-12
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def Ell_base(tau,z,N): return -600.0*C_x(z,tau,N)
def solve_a0a1(z,N,t1,t2):
    q1=cmath.exp(2j*math.pi*t1); q2=cmath.exp(2j*math.pi*t2)
    v1=Ell_base(t1,z,N); v2=Ell_base(t2,z,N)
    den=q1-q2; sc=max(abs(q1),abs(q2),1.0)
    if abs(den)<=ABS*sc: return None,None,'den~0'
    a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1,''
def fit_scale(z_fit,N,t1,t2):
    a0,_ = solve_a0a1(z_fit,N,t1,t2)[:2]
    y=cmath.exp(2j*math.pi*z_fit); chi=-1.0/y+101.0
    return (chi/a0) if (a0 is not None and a0!=0) else complex('nan')
try:
    N=360; t1=0.12+3.4j; t2=0.19+2.7j; zs=[0.21,0.23,0.25,0.27,0.29,0.31]; zfit=0.25
    S=fit_scale(zfit,N,t1,t2)
    print('\t'.join(['z','y.re','y.im','a0.re','a0.im','chi_y.re','chi_y.im','rel_q0','a1.re','a1.im','|q1|','|q2|','scale.re','scale.im','Note']))
    q1abs=abs(cmath.exp(2j*math.pi*t1)); q2abs=abs(cmath.exp(2j*math.pi*t2))
    for z in zs:
        y=cmath.exp(2j*math.pi*z); chi=-1.0/y+101.0
        try:
            a0,a1,note = solve_a0a1(z,N,t1,t2)
            if a0 is None:\n                print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chi.real),f(chi.imag),'NaN','NaN','NaN',f(q1abs),f(q2abs),f(S.real),f(S.imag),note])); continue
            a0s = S*a0
            rel = abs(a0s-chi)/(abs(chi) if abs(chi)>ABS else 1.0)
