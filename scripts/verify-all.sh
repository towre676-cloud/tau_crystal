#!/usr/bin/env bash
set -u
PYBIN="$(command -v python3 || command -v python || true)"
[ -z "$PYBIN" ] && { echo "[verify] python not found"; exit 0; }
"$PYBIN" - <<'PY'
import os, glob, json, hashlib, base64, subprocess, shutil, tempfile, sys
files=sorted(glob.glob("manifests/*.json"))
if not files:
    print("[verify] no manifests"); sys.exit(0)
openssl=shutil.which("openssl")
ok=True
for f in files:
    try:
        doc=json.load(open(f,"r",encoding="utf-8"))
        core={k:doc[k] for k in ("kind","version","process","tau","residue","witness","sustainability") if k in doc}
        canon=json.dumps(core, ensure_ascii=False, separators=(",",":"))
        calc="sha256:"+hashlib.sha256(canon.encode("utf-8")).hexdigest()
        digest=(doc.get("attest") or {}).get("merkle_root","")
        if digest!=calc:
            print("[hash mismatch]", os.path.basename(f)); ok=False
        sig=(doc.get("attest") or {}).get("signature","")
        pub=(doc.get("attest") or {}).get("public_key_pem","")
        if sig and pub and openssl and digest.startswith("sha256:"):
            hexmsg=digest.split("sha256:",1)[1]
            with tempfile.NamedTemporaryFile(delete=False) as m:
                m.write(bytes.fromhex(hexmsg)); m.flush()
                p=subprocess.run([openssl,"pkeyutl","-verify","-pubin","-inkey","/dev/stdin","-sigfile","/dev/stdin","-rawin","-in",m.name],
                                 input=pub.encode()+b"\n"+base64.b64decode(sig), capture_output=True)
            if p.returncode!=0:
                print("[sig fail]", os.path.basename(f)); ok=False
    except Exception as e:
        print("[verify error]", os.path.basename(f), e); ok=False
print("[verify] OK" if ok else "[verify] FAIL")
sys.exit(0 if ok else 1)
PY
