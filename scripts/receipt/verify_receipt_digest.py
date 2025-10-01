#!/usr/bin/env python3
import sys, json, hashlib, os
def sha256(b): h=hashlib.sha256(); h.update(b); return h.hexdigest()
def main():
    ok=True
    for rp in sys.argv[1:]:
        with open(rp,"r",encoding="utf-8") as f: r=json.load(f)
        sp=r["source"]["path"]
        want=r["digests"]["sha256"]
        with open(sp,"rb") as cf: got=sha256(cf.read())
        same=(want==got)
        print(f"[verify] {os.path.basename(rp)} sha_match={same}")
        ok = ok and same
    sys.exit(0 if ok else 1)
if __name__=="__main__": main()
