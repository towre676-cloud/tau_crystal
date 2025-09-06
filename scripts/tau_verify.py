#!/usr/bin/env python3
import json, os, sys, hashlib, tarfile, zipfile, glob, re
from pathlib import Path

REPO = Path.cwd()
MONO_DIR = REPO / "docs" / "monographs"
MANIFEST_JSON = REPO / "tau-crystal-manifest.json"
RECEIPT_JSON  = REPO / "tau-crystal-receipt.json"
ARCHIVE_TGZ   = REPO / "docs" / "monographs.tar.gz"
ARCHIVE_ZIP   = REPO / "docs" / "monographs.zip"

def fail(msg): print(f"[FAIL] {msg}", file=sys.stderr); sys.exit(1)
def ok(msg):   print(f"[OK] {msg}")

def sha256_file(p:Path):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()

def merkle_root(hexes):
    L = sorted([h.lower() for h in hexes])
    if not L: fail("no inputs for merkle_root")
    cur = L[:]
    while len(cur)>1:
        nxt=[]
        for i in range(0,len(cur),2):
            a=cur[i]
            b=cur[i] if i+1==len(cur) else cur[i+1]
            nxt.append(hashlib.sha256(bytes.fromhex(a+b)).hexdigest())
        cur=nxt
    return cur[0]

def load_json(p:Path):
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return None

man = load_json(MANIFEST_JSON)

# If there is no manifest yet, derive inputs from live monographs and just verify existence+hash deterministically.
if man is None:
    files = sorted(MONO_DIR.glob("*.md"))
    if not files:
        fail("no monographs found and no manifest present")
    included = [{"path": f.as_posix(), "sha256": sha256_file(f)} for f in files]
    root = merkle_root([e["sha256"] for e in included])
    ok(f"derived set ok; merkle_root={root}")
    sys.exit(0)

# When manifest exists, it is the source of truth.
if man.get("kind") != "tau-crystal-manifest":
    fail("manifest kind mismatch")

# 1) included files present + hashes match
calc = []
def _normalize_path(s:str)->Path:
    # treat Windows drive paths as absolute; strip to repo-relative if possible
    # keep only the suffix starting at '/docs/' or '\\docs\\' if present
    s0=s
    if re.match(r'^[A-Za-z]:[\\/]', s0):
        m=re.search(r'([\\/])docs([\\/]).*', s0)
        if m:
            s0 = s0[m.start():].replace('\\','/')
        else:
            # fallback: drop drive and backslashes
            s0 = s0.split(':',1)[-1].lstrip('\\/').replace('\\','/')
    return Path(s0)

for e in man.get("included_files", []):
    p = (REPO / _normalize_path(e["path"]).as_posix()).resolve()
    if not p.exists():
        fail(f"missing file: {p}")
    h = sha256_file(p)
    if h != e["sha256"]:
        fail(f"hash mismatch: {p} manifest={e['sha256']} actual={h}")
    calc.append(h)
ok("included files present and hashed")

# 2) merkle matches
root = merkle_root(calc)
if root != man.get("merkle_root","").lower():
    fail(f"merkle_root mismatch: manifest={man.get('merkle_root')} recomputed={root}")
ok(f"merkle_root ok: {root}")

# 3) archives (if declared)
for a in man.get("archives", []):
    ap = REPO / a["path"]
    if not ap.exists():
        fail(f"missing archive: {ap}")
    if a.get("alg") not in ("tar.gz","zip"):
        fail(f"unsupported archive alg: {a.get('alg')}")
    if sha256_file(ap) != a["sha256"]:
        fail(f"archive hash mismatch: {ap}")
ok("archives verified (or none declared)")

# 4) receipt mirror (if present)
rec = load_json(RECEIPT_JSON)
if rec:
    if rec.get("kind") != "tau-crystal-receipt":
        fail("receipt kind mismatch")
    refl = rec.get("reflective", {})
    if refl.get("merkle_root","").lower() != root:
        fail("receipt/manifest merkle mismatch")
ok("receipt reflective ok (or no receipt)")

print("[PASS] tau_verify completed")
