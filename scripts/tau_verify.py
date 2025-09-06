#!/usr/bin/env python3
import json, os, sys, hashlib, subprocess, tempfile

MANIFEST_JSON = "tau-crystal-manifest.json"
RECEIPT_JSON  = "tau-crystal-receipt.json"

def eprint(*a): print(*a, file=sys.stderr)
def require(c, m): 
    if not c: eprint("[FAIL]", m); sys.exit(1)

def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()

def merkle_root(hexes):
    L = sorted([h.lower() for h in hexes])
    if not L: return None
    cur = L[:]
    while len(cur)>1:
        nxt=[]
        for i in range(0,len(cur),2):
            a=cur[i]; b=cur[i] if i+1==len(cur) else cur[i+1]
            nxt.append(hashlib.sha256(bytes.fromhex(a+b)).hexdigest())
        cur=nxt
    return cur[0]

def read_json(p):
    if not os.path.exists(p): return {}
    with open(p,"r",encoding="utf-8") as f: return json.load(f)

def git_show(path, rev="HEAD^"):
    try:
        out = subprocess.check_output(["git","show",f"{rev}:{path}"], stderr=subprocess.STDOUT)
        return out.decode("utf-8","replace")
    except subprocess.CalledProcessError:
        return None

def openssl_verify(pubkey_path, sig_path, message_bytes):
    with tempfile.NamedTemporaryFile(delete=False) as tf:
        tf.write(message_bytes); tf.flush()
        msg = tf.name
    try:
        proc = subprocess.run(["openssl","dgst","-sha256","-verify",pubkey_path,"-signature",sig_path,msg],
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        return ("Verified OK" in proc.stdout), proc.stdout.strip()
    finally:
        try: os.unlink(msg)
        except: pass

def main():
    man = read_json(MANIFEST_JSON); rec = read_json(RECEIPT_JSON)
    require(man.get("kind") in ("tau-crystal-manifest","tau-crystal-manifest"), "bad manifest.kind")
    inc = man.get("included_files",[])
    require(isinstance(inc,list) and inc, "included_files empty")

    # 1) file hashes
    calc=[]
    for e in inc:
        require(isinstance(e,dict) and "path" in e and "sha256" in e, "bad included_files entry")
        p, h = e["path"], e["sha256"].lower()
        require(os.path.exists(p), f"missing file: {p}")
        require(sha256_file(p)==h, f"hash mismatch: {p}")
        calc.append(h)

    # 2) archives with alg
    for a in man.get("archives",[]):
        require(all(k in a for k in ("path","sha256","alg")), "archive missing fields")
        require(os.path.exists(a["path"]), f"archive missing: {a['path']}")
        require(sha256_file(a["path"]).lower()==a["sha256"].lower(), f"archive hash mismatch: {a['path']}")
        require(a["alg"] in ("tar.gz","zip"), f"unsupported archive alg: {a['alg']}")

    # 3) merkle
    m_expected = man.get("merkle_root","").lower(); require(m_expected, "missing merkle_root")
    m_calc = merkle_root(calc); require(m_calc==m_expected, f"merkle mismatch: {m_calc} != {m_expected}")

    # 4) chain
    prev = git_show(MANIFEST_JSON, "HEAD^")
    if prev:
        try:
            pj=json.loads(prev); pr=pj.get("merkle_root","").lower(); require(pr, "prev missing merkle_root")
            require(man.get("prev_merkle_root","").lower()==pr, "prev_merkle_root mismatch against previous commit")
        except Exception as ex:
            require(False, f"prev parse error: {ex}")

    # 5) receipt mirror
    if rec:
        require(rec.get("kind")=="tau-crystal-receipt", "receipt.kind mismatch")
        ref = rec.get("reflective",{})
        require(ref.get("merkle_root","").lower()==m_expected, "receipt->manifest merkle mismatch")
        for e in ref.get("files",[]):
            require(os.path.exists(e["path"]), f"receipt file missing: {e['path']}")
            require(sha256_file(e["path"]).lower()==e["sha256"].lower(), f"receipt hash mismatch: {e['path']}")
        for a in ref.get("archives",[]):
            require(os.path.exists(a["path"]), f"receipt archive missing: {a['path']}")
            require(sha256_file(a["path"]).lower()==a["sha256"].lower(), f"receipt archive hash mismatch: {a['path']}")

    # 6) optional threshold sigs against message=root + '\n' + timestamp
    thr = int(os.getenv("SIGNATURE_THRESHOLD","0"))
    if thr>0:
        msg = (man["merkle_root"]+"\n"+man.get("timestamp_utc","")).encode("utf-8")
        sig_entries = man.get("signatures",[])
        ok=0; tried=0
        for s in sig_entries:
            pub, sig = s.get("pubkey",""), s.get("signature","")
            if not (pub and sig and os.path.exists(pub) and os.path.exists(sig)): continue
            tried += 1
            good, out = openssl_verify(pub, sig, msg)
            if good: ok+=1
        require(tried>=thr and ok>=thr, f"threshold signatures invalid: ok={ok} tried={tried} need={thr}")

    # 7) optional PoW
    pow_bits = int(os.getenv("PROOF_OF_WORK_BITS","0"))
    if pow_bits>0:
        powo = man.get("pow",{})
        nonce = str(powo.get("nonce","")); ts = man.get("timestamp_utc","")
        require(nonce and ts, "PoW enabled but nonce/timestamp missing")
        d = hashlib.sha256((man["merkle_root"]+"|"+ts+"|"+nonce).encode()).digest()
        # count leading zero bits
        lb=0
        for byte in d:
            if byte==0: lb+=8; continue
            for bit in (7,6,5,4,3,2,1,0):
                if (byte>>bit)&1==0: lb+=1
                else: break
            break
        require(lb>=pow_bits, f"PoW leading bits {lb} < {pow_bits}")

    # 8) optional anchors presence
    for a in man.get("anchors",[]):
        require("type" in a and "path" in a, "anchor missing fields")
        require(os.path.exists(a["path"]), f"anchor artifact missing: {a['path']}")
        if "sha256" in a:
            require(sha256_file(a["path"]).lower()==a["sha256"].lower(), f"anchor sha mismatch: {a['path']}")

    print("[OK] τ‑Crystal docs verification passed.")
    return 0

if __name__=="__main__": sys.exit(main())
