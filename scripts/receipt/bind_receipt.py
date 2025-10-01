#!/usr/bin/env python3
import sys, os, json, hashlib, time
def sha256(b: bytes) -> str:
    h=hashlib.sha256(); h.update(b); return h.hexdigest()
def main():
    if len(sys.argv)!=2: print("usage: bind_receipt.py <canon.json>", file=sys.stderr); sys.exit(2)
    path=sys.argv[1]
    if not path.endswith(".json") or not os.path.isfile(path):
        print(f"[bind] bad path: {path}", file=sys.stderr); sys.exit(3)
    data=open(path,"rb").read()
    if len(data)==0:
        print(f"[bind] empty file: {path}", file=sys.stderr); sys.exit(4)
    # Ensure it is a single JSON value (no trailing junk)
    try:
        obj=json.loads(data.decode("utf-8"))
    except Exception as e:
        print(f"[bind] JSON parse failed: {e}", file=sys.stderr); sys.exit(5)
    # Compute content hash on exact canon bytes
    content_sha=sha256(data)
    size=len(data)
    # Derive ledger name
    base=os.path.splitext(os.path.basename(path))[0]
    stamp=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    ledger_dir=".tau_ledger"
    os.makedirs(ledger_dir, exist_ok=True)
    # Path binding (hash the absolute path string, not file contents)
    apath=os.path.abspath(path)
    path_sha=sha256(apath.encode("utf-8"))
    receipt={
        "kind":"receipt",
        "version":"1.0",
        "source":{"path":apath,"path_sha256":path_sha,"bytes":size},
        "digests":{"sha256":content_sha},
        "time_utc":stamp,
        "name":base
    }
    out=os.path.join(ledger_dir, f"{base}_{stamp}.receipt.json")
    s=json.dumps(receipt, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    open(out,"wb").write(s.encode("utf-8"))
    print(out)
if __name__=="__main__": main()
