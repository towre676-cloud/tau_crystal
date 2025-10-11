import csv, json, numpy as np, sys, math
from pathlib import Path
tol = 5e-3
pdg = json.loads(Path('tau_crystal/data/pdg/constants.json').read_text())
sing = np.loadtxt('obstruction_card/out/singular_values.csv',delimiter=',')[0]
thetaW = float(np.loadtxt('obstruction_card/out/thetaW.csv',delimiter=','))
theta_detM = float(np.loadtxt('obstruction_card/out/theta_detM.csv',delimiter=','))
fail=False
def rel_err(a,b): return abs(a-b)/max(abs(a),abs(b),1e-18)
for name,val in pdg['masses'].items():
    idx=int(val['index']); exp=float(val['value']); err=rel_err(sing[idx],exp)
    print(f'{name}: {sing[idx]:.5e} vs {exp:.5e} (Δ={err:.2e})')
    if err>tol: fail=True
exp_thetaW=pdg['angles']['thetaW']; eW=rel_err(thetaW,exp_thetaW)
print(f'thetaW: {thetaW:.6f} vs {exp_thetaW:.6f} (Δ={eW:.2e})')
if eW>tol: fail=True
print(f'theta(detM): {theta_detM:.6e}')  # should be near zero
if fail: sys.exit('PDG comparison failed')
