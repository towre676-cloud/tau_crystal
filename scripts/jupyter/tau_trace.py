# tau_trace.py — IPython cell magic: verifiable Jupyter cell receipts (no deps)
# Usage in a notebook:
#   %load_ext tau_trace
#   %%tau_trace label="demo" include_result=True
#   <your code...>
from __future__ import annotations
import hashlib, io, json, os, re, sys, time
from datetime import datetime, timezone

def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def _norm(s: str) -> bytes:
    return s.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8", "surrogatepass")

def _now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

def _safe_bool(val: str | None, default=False) -> bool:
    if val is None: return default
    return val.lower() in ("1","true","yes","on")

def _ensure_dir(p: str):
    os.makedirs(p, exist_ok=True)

def _write_json(path: str, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(obj, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, path)

def _call_qr(witness_path: str):
    # Optional: if repo has scripts/meta/qr_witness.sh, call it to badge+stamp manifest
    root = os.getcwd()
    qr = os.path.join(root, "scripts", "meta", "qr_witness.sh")
    if os.path.isfile(qr) and os.access(qr, os.X_OK):
        try:
            import subprocess
            subprocess.run([qr, witness_path], check=False)
        except Exception:
            pass

def load_ipython_extension(ip):
    from IPython.core.magic import Magics, magics_class, cell_magic

    @magics_class
    class TauTraceMagics(Magics):
        @cell_magic
        def tau_trace(self, line, cell):
            # parse key=val args (label=, include_result=)
            kv = {}
            for m in re.finditer(r'(\w+)\s*=\s*"(.*?)"|(\w+)\s*=\s*([^\s]+)', line or ""):
                if m.group(1):
                    kv[m.group(1)] = m.group(2)
                else:
                    kv[m.group(3)] = m.group(4)
            label = kv.get("label","")
            include_result = _safe_bool(kv.get("include_result"), False)

            import contextlib
            buf_out, buf_err = io.StringIO(), io.StringIO()

            result_obj = None
            exc = None
            t0 = time.time()
            try:
                with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
                    result_obj = self.shell.run_cell(cell, store_history=False).result
            except Exception as e:
                exc = repr(e)
            dt = time.time() - t0

            src_b = _norm(cell)
            out_b = _norm(buf_out.getvalue())
            err_b = _norm(buf_err.getvalue())
            res_repr = repr(result_obj) if include_result else ""
            res_b = _norm(res_repr)

            utc = _now_utc()
            record = {
                "schema": "taucrystal/jupyter_cell/v1",
                "utc": utc,
                "label": label,
                "duration_sec": round(dt, 6),
                "source_sha256": _sha256_bytes(src_b),
                "stdout_sha256": _sha256_bytes(out_b),
                "stderr_sha256": _sha256_bytes(err_b),
                "result_repr_sha256": _sha256_bytes(res_b),
                "exception": exc,
            }

            concat = b"|".join([src_b, out_b, err_b, res_b, _norm(utc)])
            digest = _sha256_bytes(concat)
            record["witness_sha256"] = digest

            led = os.path.join(os.getcwd(), ".tau_ledger", "jupyter")
            _ensure_dir(led)
            path = os.path.join(led, f"cellv1-{utc}.json")
            _write_json(path, record)
            _call_qr(path)

            print(f"[tau_trace] witness -> {path}")
            print(f"[tau_trace] sha256:{digest}")
            if exc:
                print("[tau_trace] exception recorded (see witness).")
            return result_obj

    ip.register_magics(TauTraceMagics)

# Self-test mode (no Jupyter needed):
#   python -m scripts.jupyter.tau_trace --selftest
def _selftest():
    code = 'print("hi from τ-crystal"); 2+2'
    utc = _now_utc()
    src_b = _norm(code)
    out_b = _norm("hi from τ-crystal\n")
    err_b = _norm("")
    res_b = _norm("")  # not including result in selftest
    concat = b"|".join([src_b, out_b, err_b, res_b, _norm(utc)])
    digest = _sha256_bytes(concat)
    record = {
        "schema": "taucrystal/jupyter_cell/v1",
        "utc": utc,
        "label": "selftest",
        "duration_sec": 0.0,
        "source_sha256": _sha256_bytes(src_b),
        "stdout_sha256": _sha256_bytes(out_b),
        "stderr_sha256": _sha256_bytes(err_b),
        "result_repr_sha256": _sha256_bytes(res_b),
        "exception": None,
        "witness_sha256": digest,
    }
    led = os.path.join(os.getcwd(), ".tau_ledger", "jupyter")
    os.makedirs(led, exist_ok=True)
    path = os.path.join(led, f"cellv1-{utc}.json")
    _write_json(path, record)
    _call_qr(path)
    print(f"[selftest] witness -> {path}")
    print(f"[selftest] sha256:{digest}")

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        _selftest()
    else:
        print("This module is an IPython extension. In Jupyter: %load_ext tau_trace")
