#!/usr/bin/env python3
import math, sys, json, os

def one_loop(g0, ell, b):
    den = 1.0 - b*g0*ell
    if den == 0.0:
        raise ValueError('Landau pole (one-loop): 1 - b*g0*ell = 0')
    g = g0/den
    inv = (1.0/g) + b*ell - (1.0/g0)
    return {'g': g, 'invariant': inv}

def F_int(g, g0, ell, b, b1):
    # Integral constraint F(g)=0 for two-loop: (1/b)ln[(g(b+b1 g0))/(g0(b+b1 g))] - ell
    if g <= 0.0: return float('inf')
    num = g*(b + b1*g0)
    den = g0*(b + b1*g)
    if den <= 0.0: return float('inf')
    return (1.0/b)*math.log(num/den) - ell

def two_loop_closed(g0, ell, b, b1):
    # Exact solution for dg/dell = b g + b1 g^2 when b != 0
    if b == 0.0:
        # Falls back to separable dg/(b1 g^2) = d ell
        if b1 == 0.0: raise ValueError('Trivial beta: b=b1=0')
        den = 1.0 - b1*g0*ell
        if den == 0.0: raise ValueError('Pole (two-loop, b=0): 1 - b1*g0*ell = 0')
        return g0/den
    expo = math.exp(b*ell)
    den = b + b1*g0*(1.0 - expo)
    if den == 0.0: raise ValueError('Pole (two-loop): b + b1*g0*(1 - e^{b ell}) = 0')
    return (b*g0*expo)/den

def two_loop_numeric(g0, ell, b, b1, tol=1e-12, rtol=1e-12, itmax=200):
    # Safeguarded Newton–bisection on F_int(g)=0 with bracket below the pole
    eps = 1e-18
    # Determine safe upper bound gu below pole g* where b+b1 g* = 0 or exp pole in closed form domain
    g_pole = None
    if b1 != 0.0:
        # Algebraic singularity when b + b1 g = 0 => g = -b/b1 (not always relevant if negative)
        g_dagger = -b/b1
        g_pole = g_dagger if g_dagger > 0 else None
    gl = min(g0, 1.0e-12)
    gl = max(gl, eps)
    gu = max(g0, 1.0)
    # If we know a blow-up along ell>0, back off from the pole
    if g_pole is not None:
        gu = min(gu, 0.999999999999*g_pole)
        if gu <= gl: gu = 0.5*g_pole
    # Ensure F(gl)*F(gu) <= 0 by expanding bracket if needed
    Fl = F_int(gl, g0, ell, b, b1)
    Fu = F_int(gu, g0, ell, b, b1)
    grow = 0
    while not (Fl <= 0.0 <= Fu or Fu <= 0.0 <= Fl):
        # Expand upward unless blocked by pole; else shrink downward
        cand = gu*2.0
        if g_pole is not None and cand >= g_pole:
            gl *= 0.5
            Fl = F_int(gl, g0, ell, b, b1)
        else:
            gu = cand
            Fu = F_int(gu, g0, ell, b, b1)
        grow += 1
        if grow > 60: break
    # Hybrid solve
    g = 0.5*(gl+gu)
    Fg = F_int(g, g0, ell, b, b1)
    for it in range(itmax):
        # Newton step (finite diff derivative)
        h = max(1e-12, 1e-8*abs(g))
        Fp = (F_int(g+h, g0, ell, b, b1) - Fg)/h
        newton_ok = abs(Fp) > 0.0 and math.isfinite(Fp)
        if newton_ok:
            gn = g - Fg/Fp
        else:
            gn = g
        # If Newton fell outside bracket or NaN, bisect
        if not (gl < gn < gu) or not math.isfinite(gn):
            gn = 0.5*(gl+gu)
        Fn = F_int(gn, g0, ell, b, b1)
        # Update bracket
        if (Fl <= 0.0 and Fn <= 0.0) or (Fl >= 0.0 and Fn >= 0.0):
            gl, Fl = gn, Fn
        else:
            gu, Fu = gn, Fn
        g, Fg = gn, Fn
        # Mixed absolute/relative convergence on g and residual
        if abs(Fg) < tol and abs(gu-gl) <= rtol*(abs(gl)+abs(gu))+tol:
            return {'g': g, 'residual': abs(Fg), 'iterations': it+1, 'bracket': [gl, gu]}
    return {'g': g, 'residual': abs(Fg), 'iterations': itmax, 'bracket': [gl, gu]}

def solve(g0, ell, b, b1):
    out = {'g0': g0, 'ell': ell, 'b': b, 'b1': b1}
    try:
        one = one_loop(g0, ell, b)
        out['one'] = one
    except Exception as e:
        out['one_error'] = str(e)
    try:
        g_closed = two_loop_closed(g0, ell, b, b1)
        # certify closed form by residual
        r = abs(F_int(g_closed, g0, ell, b, b1))
        out['two'] = {'g': g_closed, 'residual': r, 'method': 'closed'}
    except Exception:
        num = two_loop_numeric(g0, ell, b, b1)
        num['method'] = 'hybrid'
        out['two'] = num
    # Derived fields requested for the receipt
    g_one = out.get('one',{}).get('g', None)
    g_two = out.get('two',{}).get('g', None)
    S_one = (g_one - g0) if g_one is not None else None
    S_two = (g_two - g0) if g_two is not None else None
    out['S_one'] = S_one
    out['S_two'] = S_two
    # Scheduler and Fisher length
    def scheduler_N(ell, b):
        x = abs(1.0 - b*ell)
        x = max(x, 1e-300)
        return (1.0/(6.0*b))*math.log(1.0/x)
    n = float(os.environ.get('RG_N', '1'))
    c = float(os.environ.get('RG_C', '1'))
    L_geo = math.sqrt(max(0.0, (n*c)/(2.0*b))) * ell if b != 0.0 else float('inf')
    out['N'] = scheduler_N(ell, b) if b != 0.0 else float('inf')
    out['L_geo'] = L_geo
    out['MU_DAGGER'] = (-b/b1) if b1 != 0.0 else None
    return out

def main(argv):
    if len(argv) < 5:
        print('usage: two_loop_solver.py g0 ell b b1', file=sys.stderr); sys.exit(2)
    g0 = float(argv[1]); ell = float(argv[2]); b = float(argv[3]); b1 = float(argv[4])
    out = solve(g0, ell, b, b1)
    print(json.dumps(out, separators=(',',':')))

if __name__ == '__main__':
    main(sys.argv)
