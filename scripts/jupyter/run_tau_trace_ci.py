# run_tau_trace_ci.py — execute a single traced "cell" via IPython
# Usage:
#   python scripts/jupyter/run_tau_trace_ci.py 'print("hello"); 2+2' ci-label
from __future__ import annotations
import os, sys
from pathlib import Path

# repo root = cwd
root = Path.cwd()
sys.path.insert(0, str(root / "scripts" / "jupyter"))

try:
    from IPython.core.interactiveshell import InteractiveShell
except Exception as e:
    print(f"[ERR] IPython not available: {e}", file=sys.stderr)
    sys.exit(2)

# load tau_trace extension (local file)
import tau_trace  # noqa: F401
ip = InteractiveShell.instance()
try:
    ip.extension_manager.load_extension("tau_trace")
except Exception:
    # try module name without package path
    ip.extension_manager.load_extension("scripts.jupyter.tau_trace")

code = sys.argv[1] if len(sys.argv) > 1 else 'print("hi from τ-crystal"); 2+2'
label = sys.argv[2] if len(sys.argv) > 2 else "ci"
cell = f'%%tau_trace label="{label}" include_result=True\n{code}'

res = ip.run_cell(cell, store_history=False)
# non-fatal even if the code errors; witness will record exception
print("[ci] run complete; success:", getattr(res, "success", True))
