#!/usr/bin/env python3
import json, time, math, argparse, sys
import numpy as np
np.seterr(all="ignore")

def l2(v): return float(np.sqrt(np.mean(v*v)))
def d1(u,dx): return (np.roll(u,-1)-np.roll(u,1))/(2*dx)
def d2(u,dx): return (np.roll(u,-1)-2*u+np.roll(u,1))/(dx*dx)
def ko4_filter(u):  # 5-pt KO4 (no dx factor)
    return (-1.0/16.0)*(np.roll(u,-2)-4*np.roll(u,-1)+6*u-4*np.roll(u,1)+np.roll(u,2))
def smooth1(u):  # mild C^1-like smoother
    return 0.25*(np.roll(u,-1) + 2*u + np.roll(u,1))

def constraints(alpha, K, a, G, phi, dx):
    ex = np.exp(-4.0*np.clip(phi, -0.25, 0.25))  # protect exp
    phx  = d1(phi,dx); phxx = d2(phi,dx)
    H = -8.0*ex*(phxx + phx*phx) + (2.0/3.0)*(K*K) - 1.5*(a*a)
    M = d1(a,dx) - (2.0/3.0)*d1(K,dx) + 6.0*a*phx
    Cg= G + 2.0*phx
    return H, M, Cg

def rhs(alpha, K, a, G, phi, dx, params, glued, s_gate):
    # smooth-based derivatives only when glued
    _d1, _d2 = (d1, d2) if not glued else (
        lambda u,dx: d1(smooth1(u),dx),
        lambda u,dx: d2(smooth1(u),dx)
    )
    ex = np.exp(-4.0*np.clip(phi, -0.25, 0.25))
    phx  = _d1(phi,dx); phxx = _d2(phi,dx)

    beta  = 0.0
    nu_a, nu_G, nu_K, nu_phi = params["nu_a"], params["nu_G"], params["nu_K"], params["nu_phi"]
    kA, kG, kK = params["kA"], params["kG"], params["kK"]

    alpha_t = -2.0*alpha*K + 2e-3*_d2(alpha,dx) - beta*_d1(alpha,dx)
    K_t     = -alpha*( -8.0*ex*(phxx + phx*phx) ) - (kK*K) + nu_K*_d2(K,dx)
    a_t     = -kA*a + nu_a*_d2(a,dx) - 0.15*( _d1(a,dx) - (2.0/3.0)*_d1(K,dx) + 6.0*a*phx )
    G_t     = -kG*( G + 2.0*phx ) + nu_G*_d2(G,dx)
    phi_t   = -alpha*K + nu_phi*_d2(phi,dx)

    if glued:
        gate = s_gate*(1.0 - s_gate)
        alpha_t += 1e-3*gate*d2(alpha,dx)
        K_t     += 1e-3*gate*d2(K,dx)
        a_t     += 1e-3*gate*d2(a,dx)
        G_t     += 1e-3*gate*d2(G,dx)
        phi_t   += 1e-3*gate*d2(phi,dx)

    return alpha_t, K_t, a_t, G_t, phi_t

def evolve(test="gauge", N=1601, T=0.3, CFL=0.08, glued=True, seed=42, amp=0.01, sigKO=0.10, dx_ref=1.0/800.0, out=None):
    x  = np.linspace(0.0, 1.0, N); dx = x[1]-x[0]
    dt = CFL*dx; steps = max(1, int(round(T/dt))); dt = T/steps

    rng = np.random.RandomState(seed)
    if test=="gauge":
        alpha = 1.0 + amp*np.sin(2.0*math.pi*x)
        phi   = 0.5*amp*np.sin(2.0*math.pi*x)
        K = np.zeros_like(x); a = np.zeros_like(x); G = np.zeros_like(x)
    else:  # robust
        noise = lambda: 1e-6*rng.randn(N)
        alpha = 1.0 + noise(); phi = noise(); K = noise(); a = noise(); G = noise()

    params = dict(nu_a=1e-3, nu_G=1e-3, nu_K=1e-3, nu_phi=1e-3, kA=0.1, kG=0.1, kK=0.05)

    # corridor gate
    s = np.zeros_like(x); left=x<=0.30; right=x>=0.70; mid=(~left)&(~right)
    s[left]=0.0; s[right]=1.0; xi=(x[mid]-0.30)/(0.40); s[mid]=0.5-0.5*np.cos(math.pi*xi)
    s_gate = s

    # CORRECT scaling: stronger KO on coarser grids
    sKO = sigKO * (dx/dx_ref)**4

    # time-integrated constraints
    IH = IM = IC = 0.0

    def ok(*arrs): return all(np.all(np.isfinite(a)) for a in arrs)
    stable = True

    for _ in range(steps):
        H, M, Cg = constraints(alpha, K, a, G, phi, dx)
        if not ok(H,M,Cg,alpha,K,a,G,phi): stable=False; break
        IH += l2(H)*dt; IM += l2(M)*dt; IC += l2(Cg)*dt

        # SSPRK3 with KO and light alpha clamp
        # stage 1
        f1 = rhs(alpha,K,a,G,phi,dx,params,glued,s_gate)
        a1  = [u + dt*ut for u,ut in zip((alpha,K,a,G,phi), f1)]
        a1  = [u + sKO*ko4_filter(u) for u in a1]
        a1[0] = np.clip(a1[0], 0.3, 2.5)  # alpha

        # stage 2
        f2 = rhs(*a1, dx, params, glued, s_gate)
        a2  = [0.75*u0 + 0.25*(u1 + dt*ut) for u0,u1,ut in zip((alpha,K,a,G,phi), a1, f2)]
        a2  = [u + sKO*ko4_filter(u) for u in a2]
        a2[0] = np.clip(a2[0], 0.3, 2.5)

        # stage 3
        f3 = rhs(*a2, dx, params, glued, s_gate)
        nxt = [ (1.0/3.0)*u0 + (2.0/3.0)*(u2 + dt*ut) for u0,u2,ut in zip((alpha,K,a,G,phi), a2, f3) ]
        nxt = [u + sKO*ko4_filter(u) for u in nxt]
        nxt[0] = np.clip(nxt[0], 0.3, 2.5)

        alpha, K, a, G, phi = nxt

    Hf, Mf, Cf = constraints(alpha, K, a, G, phi, dx)
    rec = dict(
        stamp=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),
        test=test, N=N, dx=dx, T=T, steps=steps, glued=bool(glued),
        params=dict(CFL=CFL, amp=amp, sigKO=float(sKO), dx=dx),
        norms=dict(final=dict(H=l2(Hf), M=l2(Mf), C_Gamma=l2(Cf)),
                   integrated=dict(H=IH, M=IM, C_Gamma=IC)),
        stable=bool(stable),
        notes="SSPRK3 + KO4(proper dx^4) + exp-clip + alpha clamp"
    )
    outp = out or f".tau_ledger/freed/z4c_run_{rec['stamp']}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(rec,f,indent=2)
    print(outp)
    return 0

if __name__=="__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--test", choices=["gauge","robust"], default="gauge")
    ap.add_argument("--res",  type=int, default=1601)
    ap.add_argument("--T",    type=float, default=0.3)
    ap.add_argument("--CFL",  type=float, default=0.08)
    ap.add_argument("--amp",  type=float, default=0.01)
    ap.add_argument("--glued", type=str, default="True")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--sigKO", type=float, default=0.10)
    args = ap.parse_args()
    glued = (str(args.glued).lower() in ["1","true","yes","y"])
    sys.exit(evolve(args.test, args.res, args.T, args.CFL, glued, args.seed, args.amp, args.sigKO))
