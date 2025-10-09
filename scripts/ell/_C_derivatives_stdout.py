import cmath, math, traceback
from ell_theta_cubic import C_x
def f(x):\n    try: return f"{float(x):.16g}"\n    except: return 'NaN'
print('\t'.join(['z','ReTau','ImTau','N','ReC','ImC','Note']))
try:
    N=360; tau=0.12+3.4j
    for z in [0.21,0.25,0.31]:
        try:\n            C=C_x(z,tau,N); print('\t'.join([f(z),f(tau.real),f(tau.imag),f(N),f(C.real),f(C.imag),'']))\n        except Exception as e:\n            note=str(e).encode('ascii','ignore').decode('ascii'); print('\t'.join([f(z),f(tau.real),f(tau.imag),f(N),'NaN','NaN',note]))
except Exception as e:\n    note=('TOPLEVEL:'+''.join(traceback.format_exc()).splitlines()[-1]).encode('ascii','ignore').decode('ascii'); print('\t'.join(['NaN','NaN','NaN','NaN','NaN','NaN',note]))
