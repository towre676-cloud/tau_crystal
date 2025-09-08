#!/usr/bin/env python3
import json,os,sys,hashlib,base64,subprocess,tempfile
cands=[".tau_ledger/receipt.json","tau-crystal-receipt.json",".tau_ledger/manifest.json"]
p=next((x for x in cands if os.path.exists(x)),None)
if not p: print("FAIL: no manifest/receipt found"); sys.exit(1)
doc=json.load(open(p,"r",encoding="utf-8"))
d2={k:v for k,v in doc.items() if k not in {"signature","digest"}}
payload=json.dumps(d2,separators=(",",":")).encode("utf-8")
dg=hashlib.sha256(payload).hexdigest()
if doc.get("digest")!=dg: print("FAIL: digest mismatch"); sys.exit(1)
pub=".tau_ledger/pubkey.pem"; sig=doc.get("signature")
if not os.path.exists(pub) or not sig:
  print(f"OK: integrity verified (sha256={dg[:12]}...) — no signature key present")
  sys.exit(0)
with tempfile.NamedTemporaryFile(delete=False) as m, tempfile.NamedTemporaryFile(delete=False) as s:
  m.write(payload); m.flush(); s.write(base64.b64decode(sig)); s.flush()
r=subprocess.run(["openssl","pkeyutl","-verify","-pubin","-inkey",pub,"-rawin","-in",m.name,"-sigfile",s.name],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
if r.returncode==0: print(f"OK: signature (ed25519) + integrity verified (sha256={dg[:12]}...)"); sys.exit(0)
print("FAIL: signature verification failed"); sys.exit(1)
