import os, sys, json, time, math, hashlib, tempfile, subprocess, shutil

INFILE   = sys.argv[1] if len(sys.argv) > 1 else "tmp/P2P.ndjson"
OUTDIR   = "manifests"
PRIV     = "keys/erp_ed25519_private.pem"
PUB      = "keys/erp_ed25519_public.pem"
TAU_MIN  = float(os.getenv("TAU_MIN","0.05"))
TAU_SLOPE= float(os.getenv("TAU_SLOPE","0.25"))
KAPPA    = 0.1591549431

os.makedirs(OUTDIR, exist_ok=True)
state = {}

def tau_inc(elapsed, slope, tau_min):
    if elapsed <= 0: return 0.0
    x = math.tanh(slope * elapsed)
    u = 1.0 - x
    u = -1.0 if u < -1.0 else (1.0 if u > 1.0 else u)
    t = math.acos(u) / math.pi
    return t if t > tau_min else tau_min

def update(evt):
    pid = evt["process_id"]; now = time.time()
    s = state.get(pid)
    if s is None:
        s = state[pid] = {
            "tau":[0.0], "last":now, "prev":"", "qcro":[],
            "ev_sha":"sha256:"+hashlib.sha256(b"").hexdigest(),
            "pivot":"sha256:"+hashlib.sha256(b"").hexdigest()
        }
    dt = max(0.0, now - s["last"]); s["last"] = now
    s["tau"].append(round(s["tau"][-1] + tau_inc(dt, TAU_SLOPE, TAU_MIN), 6))
    seg = str(evt.get("segment","")).lower()
    mode, amp = "nominal", 0.0
    if "split" in seg: mode, amp = "split_receipt", 0.6
    if "backorder" in seg: mode, amp = "backorder", 0.7
    if "rework" in seg: mode, amp = "rework", 0.5
    s["qcro"].append({"t": s["tau"][-1], "mode": mode, "amp": amp})
    enc = json.dumps(evt, separators=(",",":"), ensure_ascii=False).encode("utf-8")
    s["ev_sha"] = "sha256:" + hashlib.sha256((s["ev_sha"] + "|").encode() + enc).hexdigest()
    return s

def residue_window(q):
    a = [e["amp"] for e in q[-8:]]
    if not a: return 0.0, 0.0
    m = sum(a)/len(a)
    r = (sum(x*x for x in a))**0.5
    d = (sum((x-m)*(x-m) for x in a))**0.5
    return r, d

def core_digest(doc_core):
    canon = json.dumps(doc_core, ensure_ascii=False, separators=(",",":"))
    return "sha256:" + hashlib.sha256(canon.encode("utf-8")).hexdigest()

def sign_digest(digest):
    openssl = shutil.which("openssl")
    if not openssl or not os.path.isfile(PRIV) or not os.path.isfile(PUB) or not digest.startswith("sha256:"):
        return None, None
    hexmsg = digest.split("sha256:",1)[1]
    with tempfile.NamedTemporaryFile(delete=False) as m:
        m.write(bytes.fromhex(hexmsg)); m.flush()
        r = subprocess.run([openssl,"pkeyutl","-sign","-inkey",PRIV,"-rawin","-in",m.name], capture_output=True)
    if r.returncode != 0: return None, None
    import base64
    return base64.b64encode(r.stdout).decode("ascii"), open(PUB,"r",encoding="utf-8",errors="ignore").read()

def write_manifest(doc_core):
    digest = core_digest(doc_core)
    attest = {"merkle_root": digest, "signed_by":"", "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    sig, pub = sign_digest(digest)
    if sig and pub:
        attest["signed_by"] = "ed25519:org-key-2025"
        attest["signature"] = sig
        attest["public_key_pem"] = pub
    full = dict(doc_core)
    full["attest"] = attest
    fname = digest.replace("sha256:","") + ".json"
    with open(os.path.join(OUTDIR, fname), "w", encoding="utf-8") as f:
        f.write(json.dumps(full, ensure_ascii=False) + "\n")
    return fname, digest

def process_line(evt):
    s = update(evt)
    Rn, Dn = residue_window(s["qcro"])
    core = {
      "kind":"tau-crystal-receipt","version":"1.2.0",
      "process":{"id":evt["process_id"],"domain":evt.get("domain","UNK"),"segment":evt.get("segment","event"),"prev_manifest":s["prev"]},
      "tau":{"t":s["tau"],"clock":"Chebyshev-decay","params":{"tau_min":TAU_MIN,"slope":TAU_SLOPE}},
      "residue":{"R_norm":Rn,"D_norm":Dn,"kappa":KAPPA,"qcro":s["qcro"][-4:]},
      "witness":{"events_sha":s["ev_sha"],"pivot_transcript":s["pivot"],"rank_signature":{"p":2147482951,"rank":6}},
      "sustainability":evt.get("sustainability",{})
    }
    fname, digest = write_manifest(core)
    s["prev"] = digest
    return fname

def main():
    if not os.path.isfile(INFILE):
        print(f"[process] input file not found: {INFILE}")
        return
    with open(INFILE,"r",encoding="utf-8",errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line: continue
            try:
                evt = json.loads(line)
                if "process_id" not in evt: continue
                process_line(evt)
            except Exception:
                pass

if __name__ == "__main__":
    main()
