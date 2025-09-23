#!/usr/bin/env python3
import math, sys, json
def beta(g,b,b1): return b*g + b1*(g**2)
def one_loop(mu0,g0,ell,b):
    den = 1.0 - b*g0*ell
    if den == 0.0: raise ValueError('Landau pole reached')
    g = g0/den
    inv = (1.0/g) + b*ell - (1.0/g0)
    return g, inv
def two_loop(mu0,g0,ell,b,b1,tol=1e-14,itmax=100):
    g = g0
    mu_dag = (-b/b1) if b1!=0 else None
    def F(x):
        if b!=0 and b1>0 and b>0:
            s = math.sqrt(b1/b)
            return (1.0/math.sqrt(b*b1))*(math.atan(s*x)-math.atan(s*g0)) - ell
        steps=2048; a=g0; c=x
        if c==a: return -ell
        h=(c-a)/steps; acc=0.0
        for i in range(steps+1):
            t=a+i*h; w=4.0 if i%2==1 else 2.0
            if i in (0,steps): w=1.0
            acc += w/(beta(t,b,b1))
        return (h/3.0)*acc - ell
    def dF(x): return -1.0/(beta(x,b,b1))
    for _ in range(itmax):
        if mu_dag is not None and mu_dag>0 and abs(g-mu_dag)<1e-12: raise ValueError('Domain boundary mu^dagger encountered')
        f=F(g); df=dF(g)
        if df==0.0: break
        g_new=g - f/df
        if not math.isfinite(g_new): raise ValueError('Non-finite iterate')
        if abs(g_new-g) <= tol*(1.0+abs(g)): g=g_new; break
        g=g_new
    return g, abs(F(g))
def main(argv):
    if len(argv) < 2:
        print('usage: two_loop_solver.py <mode:one|two> ...'); sys.exit(2)
    mode=argv[1]
    if mode=='one':
        if len(argv) < 6:
            print('usage: two_loop_solver.py one mu0 g0 ell b'); sys.exit(2)
        mu0=float(argv[2]); g0=float(argv[3]); ell=float(argv[4]); b=float(argv[5])
        g,inv=one_loop(mu0,g0,ell,b); out={'mode':'one','mu0':mu0,'g0':g0,'ell':ell,'b':b,'g':g,'invariant':inv}
    elif mode=='two':
        if len(argv) < 7:
            print('usage: two_loop_solver.py two mu0 g0 ell b b1'); sys.exit(2)
        mu0=float(argv[2]); g0=float(argv[3]); ell=float(argv[4]); b=float(argv[5]); b1=float(argv[6])
        g,res=two_loop(mu0,g0,ell,b,b1); out={'mode':'two','mu0':mu0,'g0':g0,'ell':ell,'b':b,'b1':b1,'g':g,'residual':res}
    else:
        print('unknown mode'); sys.exit(2)
    print(json.dumps(out,separators=(',',':')))
if __name__=='__main__': main(sys.argv)
