import sys, json, subprocess, base64, os, tempfile, pathlib
priv="keys/erp_ed25519_private.pem"; pub="keys/erp_ed25519_public.pem"
have_ssl = (subprocess.call(["bash","-lc","command -v openssl >/dev/null 2>&1"])==0)
outdir = sys.argv[1] if len(sys.argv)>1 else "manifests"
pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)
for line in sys.stdin:
    line=line.strip()
    if not line: 
        continue
    try:
        doc=json.loads(line)
    except:
        continue
    digest=doc.get("attest",{}).get("merkle_root","")
    if have_ssl and os.path.isfile(priv) and os.path.isfile(pub) and digest.startswith("sha256:"):
        hexmsg=digest.split("sha256:")[1]
        with tempfile.NamedTemporaryFile(delete=False) as m:
            m.write(bytes.fromhex(hexmsg)); m.flush()
            sig = subprocess.run(["bash","-lc",f"openssl pkeyutl -sign -inkey {priv} -rawin -in {m.name} | base64 -w0 2>/dev/null || openssl pkeyutl -sign -inkey {priv} -rawin -in {m.name} | base64"], capture_output=True).stdout.decode().strip()
        pub_pem=open(pub,"r",encoding="utf-8", errors="ignore").read()
        doc.setdefault("attest",{})["signed_by"]="ed25519:org-key-2025"
        doc["attest"]["signature"]=sig
        doc["attest"]["public_key_pem"]=pub_pem
    fname=(digest.replace("sha256:","") or "unsigned-"+str(abs(hash(line)) ))+".json"
    payload=json.dumps(doc,ensure_ascii=False)
    open(os.path.join(outdir,fname),"w",encoding="utf-8").write(payload+"\n")
    sys.stdout.write(payload+"\n"); sys.stdout.flush()
