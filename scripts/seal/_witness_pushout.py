import json,hashlib
from pathlib import Path
m=json.loads(Path("artifacts/seal/pushout_manifest.json").read_text())
canon=json.dumps(m,separators=(",",":"))
H=hashlib.sha256(canon.encode()).hexdigest()
cert=json.loads(Path("artifacts/seal/verifier_certificate.json").read_text())
ok=(cert.get("H_τ")==H and cert.get("terminal",False))
w={"universal_ok":ok,"H_tau":H,"terminal":cert.get("terminal",False)}
Path("artifacts/seal/universal_witness.json").write_text(json.dumps(w,separators=(",",":")))
