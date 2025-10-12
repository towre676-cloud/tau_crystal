import argparse, sys
try:
    from mpmath import mp
except Exception as e:
    print('mpmath not available. install with: python3 -m pip install --user mpmath'); sys.exit(2)
try:
    from cert.modforms import e_series_coeffs, eval_series, D_eval, choose_N_for_tol
except Exception as e:
    print('import failed: cert.modforms not found. ensure cert/__init__.py and cert/modforms.py exist.'); sys.exit(3)

ap = argparse.ArgumentParser()
ap.add_argument('--t', type=float, default=1.0)
ap.add_argument('--prec', type=int, default=120)
args = ap.parse_args()
mp.mp.dps = args.prec
tau = 1j*mp.mpf(args.t)
q = mp.exp(2j*mp.pi*tau)
qa = abs(q)
N = choose_N_for_tol(qa, args.prec)
a2,a4,a6 = e_series_coeffs(N)
E2=eval_series(a2,q); E4=eval_series(a4,q); E6=eval_series(a6,q)
DE2=D_eval(a2,q); DE4=D_eval(a4,q); DE6=D_eval(a6,q)
r1 = abs(DE2 - (E2*E2 - E4)/12)
r2 = abs(DE4 - (E2*E4 - E6)/3)
r3 = abs(DE6 - (E2*E6 - E4*E4)/2)
print(f't={args.t} prec={args.prec} N={N} |q|={qa:.3e}')
print('residuals:', r1, r2, r3)
print('max_residual:', max(r1,r2,r3))
