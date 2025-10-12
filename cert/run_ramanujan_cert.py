import json, hashlib, sys, argparse
from mpmath import mp, exp, pi
from modforms import e_series_coeffs, eval_series, D_eval, choose_N_for_tol
def verify_point(tau, digits):
    mp.mp.dps = digits
    q = exp(2j*pi*tau); qa = abs(q)
    N = choose_N_for_tol(qa, digits)
    a2,a4,a6 = e_series_coeffs(N)
    E2 = eval_series(a2,q); E4 = eval_series(a4,q); E6 = eval_series(a6,q)
    DE2 = D_eval(a2,q); DE4 = D_eval(a4,q); DE6 = D_eval(a6,q)
    r1 = abs(DE2 - (E2*E2 - E4)/12)
    r2 = abs(DE4 - (E2*E4 - E6)/3)
    r3 = abs(DE6 - (E2*E6 - E4*E4)/2)
    return {'tau_re': float(mp.re(tau)), 'tau_im': float(mp.im(tau)), 'q_abs': float(qa), 'N': int(N), 'digits': int(digits), 'residuals': {'DE2': str(r1), 'DE4': str(r2), 'DE6': str(r3)}, 'max_residual': str(max(r1,r2,r3))}
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--taus', default='0.8,1.0,1.5')
    ap.add_argument('--prec', type=int, default=200)
    args = ap.parse_args()
    ts = [mp.mpf(x) for x in args.taus.split(',') if x]
    results = []
    for t in ts:
        tau = 1j*t
        results.append(verify_point(tau, args.prec))
    maxres = max([mp.mpf(r['max_residual']) for r in results])
    payload = {'kind':'ramanujan_cert','precision_digits':args.prec,'grid_tau_imag': [str(t) for t in ts],'results':results,'max_residual_overall': str(maxres)}
    with open(args.out,'w',encoding='utf-8') as f: json.dump(payload,f,indent=2,sort_keys=True)
    h = hashlib.sha256(json.dumps(payload, sort_keys=True).encode('utf-8')).hexdigest()
    print('OK', args.out, h)
if __name__=='__main__': main()
