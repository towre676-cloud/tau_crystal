import json,os
from pathlib import Path
def T(p):
    try: return json.loads(Path(p).read_text())
    except: return None
out={
 "manifest":T("artifacts/seal/pushout_manifest.canon.json"),
 "certificate":T("artifacts/seal/verifier_certificate.json"),
 "H_tau":(Path("artifacts/seal/.H_τ").read_text().strip() if Path("artifacts/seal/.H_τ").exists() else None)}
print(json.dumps(out,separators=(",",":")))
