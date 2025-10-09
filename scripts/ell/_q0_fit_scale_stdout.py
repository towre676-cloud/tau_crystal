import os, sys, cmath, math
sys.path.insert(0, os.path.join(os.getcwd(),'scripts','ell'))
from ell_series_x import Cx_series
ABS=1e-12
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def Ell_base(tau,z,N): return -600.0*Cx_series(z,tau,N)
def solve_a0a1(z,N,t1,t2):
    q1=cmath.exp(2j*cmath.pi*t1); q2=cmath.exp(2j*cmath.pi*t2)
    v1=Ell_base(t1,z,N); v2=Ell_base(t2,z,N)
    den=q1-q2; scale=max(abs(q1),abs(q2),1.0)
    if abs(den)<=ABS*scale: return None,None
    a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1
def main():
    # small-|q|, well separated
    N=360; t1=0.12+3.4j; t2=0.19+2.7j; zs=[0.21,0.25,0.31]
    # collect base a0 and targets chi_y
    rows=[]
    for z in zs:
        y=cmath.exp(2j*cmath.pi*z); chiy=-1.0/y+101.0
        a0,a1=solve_a0a1(z,N,t1,t2)
        rows.append((z,y,chiy,a0))
    # fit complex scale s to minimize sum |s a0 - chi_y|^2 over valid rows
    num=0+0j; den=0.0
    for (_,_,chiy,a0) in rows:
        if a0 is None: continue
        num += a0.conjugate()*chiy
        den += (a0.real*a0.real + a0.imag*a0.imag)
    s = (num/den) if den>0 else complex('nan')
    # print table
    print('\t'.join(['z','y.re','y.im','a0_base.re','a0_base.im','a0_scaled.re','a0_scaled.im','chi_y.re','chi_y.im','rel_base','rel_scaled','scale.re','scale.im']))
    for (z,y,chiy,a0) in rows:
        if a0 is None:
            print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN','NaN','NaN',f(chiy.real),f(chiy.imag),'NaN','NaN',f(float('nan')),f(float('nan'))]))
            continue
        a0s = s*a0
        rel_b = abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS else 1.0)
        rel_s = abs(a0s-chiy)/(abs(chiy) if abs(chiy)>ABS else 1.0)
        print('\t'.join([f(z),f(y.real),f(y.imag),f(a0.real),f(a0.imag),f(a0s.real),f(a0s.imag),f(chiy.real),f(chiy.imag),f(rel_b),f(rel_s),f(s.real),f(s.imag)]))
if __name__=='__main__': main()
