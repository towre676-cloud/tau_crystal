#!/usr/bin/env python3
import os,sys,hashlib,json,base64,subprocess,tempfile,time
outdir=".tau_ledger"; os.makedirs(outdir,exist_ok=True); path=os.path.join(outdir,"receipt.json")
doc={
 "kind":"tau-crystal-receipt",
 "repo": os.getenv("GITHUB_REPOSITORY",""),
 "commit": os.getenv("GITHUB_SHA",""),
 "ref": os.getenv("GITHUB_REF",""),
 "run_id": os.getenv("GITHUB_RUN_ID",""),
 "runner_os": os.getenv("RUNNER_OS",""),
 "toolchain": os.getenv("TOOLCHAIN",""),
 "mathlib_sha": os.getenv("MATHLIB_SHA",""),
 "cache_status": os.getenv("CACHE_STATUS",""),
 "elapsed_s": int(os.getenv("ELAPSED_S","0") or "0"),
 "image_tag": os.getenv("IMAGE_TAG",""),
 "timestamp": int(time.time())
}
payload=json.dumps(doc,separators=(",",":")).encode("utf-8")
digest=hashlib.sha256(payload).hexdigest(); doc["digest"]=digest
sig=None
sk_b64=os.getenv("ED25519_SK_B64"); sk_file=".tau_ledger/ed25519_sk.pem" if os.path.exists(".tau_ledger/ed25519_sk.pem") else None
try:
  if sk_b64 or sk_file:
    with tempfile.NamedTemporaryFile(delete=False) as m, tempfile.NamedTemporaryFile(delete=False) as s:
      m.write(payload); m.flush()
      keypath=None
      if sk_b64:
        with tempfile.NamedTemporaryFile(delete=False) as k:
          k.write(base64.b64decode(sk_b64)); k.flush(); keypath=k.name
      else:
        keypath=sk_file
      r=subprocess.run(["openssl","pkeyutl","-sign","-inkey",keypath,"-rawin","-in",m.name,"-out",s.name],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
      if r.returncode==0:
        sig=base64.b64encode(open(s.name,"rb").read()).decode("ascii")
except Exception as e:
  sig=None
if sig: doc["signature"]=sig
json.dump(doc,open(path,"w",encoding="utf-8"))
print(path)
