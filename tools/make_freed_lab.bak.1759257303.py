import os, json

def md(lines):
    return {"cell_type":"markdown","metadata":{},"id":"md-"+str(abs(hash(tuple(lines)))%10**8),"source":"\n".join(lines)+"\n"}

def code(lines):
    # IMPORTANT: we join with real newlines so the kernel sees proper code
    return {"cell_type":"code","metadata":{},"id":"py-"+str(abs(hash(tuple(lines)))%10**8),
            "execution_count":None,"outputs":[],"source":"\n".join(lines)+"\n"}

nb = {
  "nbformat": 4, "nbformat_minor": 5,
  "metadata": {
    "kernelspec": {"display_name":"Python 3","language":"python","name":"python3"},
    "language_info": {"name":"python","version":"3"}
  },
  "cells": [
    md([
      "# Freed RG Lab — receipts & plots",
      "",
      "This notebook pulls receipts from `analysis/freed/` and `.tau_ledger/freed/`,",
      "draws a couple of simple plots (if `matplotlib` is available), and prints a compact summary."
    ]),
    code([
      "import sys, os, glob, json, math",
      "# Windows asyncio policy to placate nbconvert on Win10/11",
      "if sys.platform.startswith('win'):",
      "    import asyncio",
      "    try:",
      "        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())",
      "    except Exception as e:",
      "        print('[info] cannot set WindowsSelectorEventLoopPolicy:', e)",
      "try:",
      "    import matplotlib",
      "    matplotlib.use('Agg')  # headless-safe",
      "    import matplotlib.pyplot as plt",
      "except Exception as e:",
      "    plt = None; print('[info] matplotlib not available:', e)",
      "",
      "def latest(pattern):",
      "    files = sorted(glob.glob(pattern))",
      "    return files[-1] if files else None",
      "",
      "def load_json(path):",
      "    try:",
      "        with open(path, 'r', encoding='utf-8') as f:",
      "            return json.load(f)",
      "    except Exception as e:",
      "        print('[warn] cannot load', path, e); return None",
      "",
      "os.makedirs('analysis/freed', exist_ok=True)"
    ]),
    md(["## Determinant identity (trace vs finite difference)"]),
    code([
      "p = latest('analysis/freed/*_determinant_identity.json')",
      "if not p:",
      "    print('[warn] no determinant_identity receipt found')",
      "else:",
      "    j = load_json(p)",
      "    xs  = [row['ell'] for row in j['grid']]",
      "    lhs = [row['lhs_tr_identity'] for row in j['grid']]",
      "    rhs = [row['rhs_fd'] for row in j['grid']]",
      "    print('[determinant] max_abs_err =', j.get('max_abs_err'))",
      "    if plt:",
      "        import matplotlib.pyplot as plt  # ensure alias",
      "        plt.figure()",
      "        plt.plot(xs, lhs, label='trace identity')",
      "        plt.plot(xs, rhs, linestyle='dashed', label='finite diff')",
      "        plt.title('trace vs d/dℓ log det Σ')",
      "        plt.legend(); plt.tight_layout(); plt.show()"
    ]),
    md(["## TMF deltas (mock elliptic correction)"]),
    code([
      "p = latest('analysis/freed/*_tmf_deltas.json')",
      "if not p:",
      "    print('[warn] no tmf_deltas receipt found (mock may be off)')",
      "else:",
      "    j = load_json(p) or {}",
      "    tmf = j.get('tmf', {})",
      "    print('[tmf] levels=', tmf.get('levels'), 'eps=', tmf.get('eps'))",
      "    for k in ('phi_off','phi_on'):",
      "        sec = tmf.get(k, {})",
      "        print(f\"[tmf {k}] delta_whole=\", sec.get('delta_whole'), ' delta_segments=', sec.get('delta_segments'))",
      "    print('[tmf] checks:', j.get('checks'))"
    ]),
    md(["## Defects (W(B₅) walls)"]),
    code([
      "p = latest('.tau_ledger/freed/defect_*.manifest.json')",
      "if not p:",
      "    print('[warn] no defect manifest found')",
      "else:",
      "    j = load_json(p) or {}",
      "    cert = j.get('certificates', {})",
      "    print('[defect] sign_flip_phase=', cert.get('sign_flip_phase'),",
      "          'perm_phase=', cert.get('perm_phase'))",
      "    print('[defect] sign_flip_shape_err=', cert.get('sign_flip_shape_err'),",
      "          'perm_shape_err=', cert.get('perm_shape_err'))"
    ]),
    md(["## Axioms summary"]),
    code([
      "from pprint import pprint",
      "p = latest('analysis/freed/axioms_*.json')",
      "if not p:",
      "    print('[warn] no axioms json found — run scripts/freed/axioms_table.py')",
      "else:",
      "    pprint(load_json(p))"
    ])
  ]
}

os.makedirs('notebooks', exist_ok=True)
out = 'notebooks/FreedLab.ipynb'
with open(out, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=2, ensure_ascii=False)
print('[ok] wrote', out)
