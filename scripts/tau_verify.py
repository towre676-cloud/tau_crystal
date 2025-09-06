#!/usr/bin/env python3
import json, os, sys, hashlib, subprocess, tempfile, shutil

MANIFEST_JSON = "tau-crystal-manifest.json"
RECEIPT_JSON  = "tau-crystal-receipt.json"

def eprint(*a): print(*a, file=sys.stderr)

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""):
            h.update(chunk)
    return h.hexdigest()

def merkle_root(hex_list):
    if not hex_list: return None
    L = sorted([s.lower() for s in hex_list])
    # In each layer, if odd number of nodes, duplicate last leaf (Bitcoin-style)
    cur = L[:]
    while len(cur) > 1:
        nxt = []
        for i in range(0, len(cur), 2):
            a = cur[i]
            b = cur[i] if i+1 == len(cur) else cur[i+1]
            data = bytes.fromhex(a + b)
            nxt.append(hashlib.sha256(data).hexdigest())
        cur = nxt
    return cur[0]

def read_json(path):
    if not os.path.exists(path): return {}
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def git_show(path, rev="HEAD^"):
    try:
        out = subprocess.check_output(["git", "show", f"{rev}:{path}"], stderr=subprocess.STDOUT)
        return out.decode("utf-8", "replace")
    except subprocess.CalledProcessError:
        return None

def openssl_verify(pubkey_path, sig_path, message_bytes):
    # openssl dgst -sha256 -verify pubkey.pem -signature file.sig /path/to/data
    with tempfile.NamedTemporaryFile(delete=False) as tf:
        tf.write(message_bytes); tf.flush()
        msg_path = tf.name
    try:
        cmd = ["openssl", "dgst", "-sha256", "-verify", pubkey_path, "-signature", sig_path, msg_path]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        ok = ("Verified OK" in proc.stdout)
        return ok, proc.stdout.strip()
    finally:
        try: os.unlink(msg_path)
        except: pass

def require(cond, msg, code=1):
    if not cond:
        eprint(f"[FAIL] {msg}")
        sys.exit(code)

def main():
    man = read_json(MANIFEST_JSON)
    rec = read_json(RECEIPT_JSON)
    require(man.get("kind") == "tau-crystal-manifest", f"{MANIFEST_JSON} missing or wrong kind")
    require(isinstance(man.get("included_files"), list) and man["included_files"], "manifest.included_files is empty")

    # 1) Verify file hashes
    calc_hashes = []
    for ent in man["included_files"]:
        require(isinstance(ent, dict) and "path" in ent and "sha256" in ent, "manifest.included_files entry malformed")
        p, h_expected = ent["path"], ent["sha256"].lower()
        require(os.path.exists(p), f"file missing: {p}")
        h_calc = sha256_file(p)
        require(h_calc == h_expected, f"sha256 mismatch for {p}: expected {h_expected}, got {h_calc}")
        calc_hashes.append(h_calc)

    # Include archives (optional)
    for ent in man.get("archives", []):
        require(isinstance(ent, dict) and "path" in ent and "sha256" in ent, "manifest.archives entry malformed")
        p, h_expected = ent["path"], ent["sha256"].lower()
        require(os.path.exists(p), f"archive missing: {p}")
        h_calc = sha256_file(p)
        require(h_calc == h_expected, f"archive sha256 mismatch for {p}: expected {h_expected}, got {h_calc}")

    # 2) Recompute Merkle and compare
    m_expected = man.get("merkle_root", "").lower()
    require(m_expected, "manifest.merkle_root missing")
    m_calc = merkle_root(calc_hashes)
    require(m_calc == m_expected, f"merkle_root mismatch: expected {m_expected}, got {m_calc}")

    # 3) Chain verification via previous commit
    prev_json = git_show(MANIFEST_JSON, "HEAD^")
    if prev_json:
        try:
            prev = json.loads(prev_json)
            prev_root = prev.get("merkle_root", "").lower()
            require(prev_root, "previous manifest present but previous merkle_root missing")
            have_prev_link = man.get("prev_merkle_root", "").lower()
            require(have_prev_link == prev_root, f"prev_merkle_root mismatch: expected {prev_root}, got {have_prev_link or '(absent)'}")
        except Exception as ex:
            require(False, f"failed to parse previous {MANIFEST_JSON}: {ex}")

    # 4) Cross-check receipt
    if rec:
        require(rec.get("kind") == "tau-crystal-receipt", "receipt.kind mismatch")
        ref = rec.get("reflective", {})
        require(ref.get("merkle_root", "").lower() == m_expected, "receipt.reflective.merkle_root != manifest.merkle_root")
        rfiles = ref.get("files", [])
        # If present, ensure each has matching hash and exists
        for ent in rfiles:
            require(isinstance(ent, dict) and "path" in ent and "sha256" in ent, "receipt.reflective.files entry malformed")
            p, h = ent["path"], ent["sha256"].lower()
            require(os.path.exists(p), f"receipt file missing: {p}")
            require(sha256_file(p) == h, f"receipt hash mismatch for {p}")

    # 5) Optional threshold signature verification
    threshold = int(os.getenv("SIGNATURE_THRESHOLD", "0"))
    if threshold > 0:
        pubdir = os.getenv("SIGNER_PUBKEYS_DIR", ".well-known/tau-crystal-signers/pubkeys")
        sigdir = os.getenv("SIGNATURES_DIR", ".well-known/tau-crystal-signers/signatures")
        message = (man["merkle_root"] + "\n" + man.get("timestamp_utc", "")).encode("utf-8")
        ok_count = 0
        tried = 0
        if os.path.isdir(pubdir) and os.path.isdir(sigdir):
            for name in sorted(os.listdir(pubdir)):
                if not name.lower().endswith((".pem", ".pub")): continue
                pub = os.path.join(pubdir, name)
                # signature file naming: same stem + .sig (or .pem.sig)
                stem = name.rsplit(".", 1)[0]
                cand = [
                    os.path.join(sigdir, stem + ".sig"),
                    os.path.join(sigdir, name + ".sig"),
                ]
                sig = next((c for c in cand if os.path.exists(c)), None)
                if not sig: continue
                tried += 1
                ok, out = openssl_verify(pub, sig, message)
                if ok: ok_count += 1
                else: eprint(f"[warn] signature failed for {name}: {out}")
        require(tried >= threshold, f"threshold signatures required={threshold}, provided={tried}")
        require(ok_count >= threshold, f"threshold signatures valid={ok_count} < required={threshold}")

    # 6) Optional PoW: require leading zero bits on H(merkle_root|timestamp|nonce)
    pow_bits = int(os.getenv("PROOF_OF_WORK_BITS", "0"))
    if pow_bits > 0:
        pow_obj = man.get("pow", {})
        nonce = str(pow_obj.get("nonce", ""))
        ts = man.get("timestamp_utc", "")
        require(nonce and ts, "PoW enabled but nonce/timestamp missing in manifest")
        msg = (man["merkle_root"] + "|" + ts + "|" + nonce).encode("utf-8")
        digest = hashlib.sha256(msg).hexdigest()
        # count leading zero bits
        leading_hex_zeros = 0
        for ch in digest:
            if ch == '0': leading_hex_zeros += 1
            else: break
        leading_bits = leading_hex_zeros * 4
        require(leading_bits >= pow_bits, f"PoW failed: leading_bits={leading_bits} < required={pow_bits}")
    print("[OK] τ‑Crystal documentation verification passed.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
