import os, json, uuid, time
def md(txt): return {"cell_type":"markdown","metadata":{},"id":uuid.uuid4().hex,"source":txt.splitlines(keepends=True)}
def code(src): return {"cell_type":"code","metadata":{},"id":uuid.uuid4().hex,"execution_count":None,"outputs":[],"source":[l+"\n" for l in src.split("\n")]}

nb = {
  "nbformat":4, "nbformat_minor":5,
  "metadata":{
    "kernelspec":{"display_name":"Python 3","language":"python","name":"python3"},
    "language_info":{"name":"python","version":"3"}
  },
  "cells":[
    md("# Freed RG Lab — receipts & plots\n\nRuns purely from `analysis/freed/` and `.tau_ledger/freed/`. If a panel has no data yet, it prints a hint.\n"),
    code(
"""import os, glob, json, math
try:
    import matplotlib.pyplot as plt
except Exception as e:
    plt = None; print('[info] matplotlib not available:', e)

def latest(pattern):
    files = sorted(glob.glob(pattern))
    return files[-1] if files else None

def load_json(path):
    try:
        with open(path, 'r', encoding='utf-8') as f: return json.load(f)
    except Exception as e:
        print('[warn] cannot load', path, e); return None

os.makedirs('analysis/freed', exist_ok=True)
"""
    ),
    md("## 1) Flatness identity (diag/mixed)"),
    code(
"""p = latest('analysis/freed/*_determinant_identity.json')
J = load_json(p) if p else None
if not J:
    print('[hint] run scripts/freed/rg_leaf_checks.py to emit determinant_identity JSON'); 
else:
    mx = J.get('max_abs_err', None)
    print('max_abs_err =', mx, ' from ', p)
    xs = [g['ell'] for g in J['grid'][:200]]
    lhs = [g['lhs_tr_identity'] for g in J['grid'][:200]]
    rhs = [g['rhs_fd'] for g in J['grid'][:200]]
    if plt:
        plt.figure(); plt.plot(xs, lhs, label='tr(Σ^{-1}∂Σ)'); plt.plot(xs, rhs, linestyle='--', label='∂ℓ log det Σ'); plt.title('Flatness identity'); plt.legend(); plt.xlabel('ℓ'); plt.ylabel('value'); plt.show()
"""
    ),
    md("## 2) Factorization (segment sum vs whole)"),
    code(
"""p0 = latest('analysis/freed/*_factorization_phi_off.json')
p1 = latest('analysis/freed/*_factorization_phi_on.json')
J0 = load_json(p0) if p0 else None
J1 = load_json(p1) if p1 else None
for tag,JJ in [('φ off',J0),('φ on',J1)]:
    if not JJ: print('[hint]', tag, 'factorization file missing'); continue
    print(tag, 'sum_segments=', JJ['sum_segments'], ' whole=', JJ['whole'], ' abs_err=', JJ['abs_err'])
"""
    ),
    md("## 3) TMF mock deltas (levels 12,18,30)"),
    code(
"""p = latest('analysis/freed/*_tmf_deltas.json')
J = load_json(p) if p else None
if not J:
    print('[hint] run verifier with FREED_TMF_MOCK=1 to emit tmf_deltas JSON')
else:
    T = J.get('tmf', {})
    print('levels=', T.get('levels'), ' eps=', T.get('eps'), ' rtol=', T.get('rtol'), ' atol=', T.get('atol'))
    for key in ('phi_off','phi_on'):
        if key in T:
            K=T[key]
            print(key, 'Δwhole=', K['delta_whole'], 'Δsegments=', K['delta_segments'], ' (baseline whole=', K['baseline_whole'], ')')
"""
    ),
    md("## 4) η-term (½·log|W|) & φ-twist"),
    code(
"""p = latest('analysis/freed/eta_tmf_*.json')
J = load_json(p) if p else None
if not J:
    print('[hint] run scripts/freed/eta_tmf_report.py to emit eta report JSON')
else:
    S = J.get('stack', {})
    print('stack=', S.get('effective'), ' |W|=', S.get('order'), ' eta_half_logW=', S.get('eta_half_logW'), ' phi_twist=', J.get('stack',{}).get('phi_twist'))
"""
    ),
    md("## 5) Defect functor (W(B5) walls)"),
    code(
"""p = latest('analysis/freed/defect_*.json')
J = load_json(p) if p else None
if not J:
    print('[hint] run scripts/freed/defect_functor.py to emit defect JSON')
else:
    print('sign_flip_phase=', J.get('sign_flip_phase'), ' perm_phase=', J.get('perm_phase'))
    print('shape_err(sign)=', J.get('sign_flip_shape_err'), ' shape_err(perm)=', J.get('perm_shape_err'))
"""
    ),
    md("## 6) Axioms summary"),
    code(
"""p = latest('analysis/freed/axioms_*.json')
J = load_json(p) if p else None
if not J:
    print('[hint] run scripts/freed/axioms_table.py to emit axioms JSON')
else:
    print('manifests counted =', J.get('manifest_count'))
    for ax in J.get('axioms', []):
        print(f"- {ax['axiom']}: {ax['status']}  (certs={len(ax.get('certificates',[]))})")
"""
    ),
  ]
}

os.makedirs('notebooks', exist_ok=True)
out = 'notebooks/FreedLab.ipynb'
with open(out, 'w', encoding='utf-8') as f: json.dump(nb, f, indent=2)
print('[ok] wrote', out)
