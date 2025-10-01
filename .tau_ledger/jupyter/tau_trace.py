from IPython.core.magic import register_line_cell_magic
import hashlib, os, time, textwrap
LEDGER=".tau_ledger/jupyter"; LOG=os.path.join(LEDGER,"trace.log")
os.makedirs(LEDGER, exist_ok=True)
@register_line_cell_magic
def tau_trace(line, cell=None):
    src=(cell or line or "").encode("utf-8")
    h=hashlib.sha256(src).hexdigest(); ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    with open(LOG,"a",encoding="utf-8") as f: f.write(f"{ts} sha256:{h} bytes:{len(src)}\\n")
    print(f"[tau_trace] {ts} sha256:{h} bytes:{len(src)}")
