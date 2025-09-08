#!/usr/bin/env python3
import json, hashlib, os, sys
CANDIDATES = ["tau-crystal-receipt.json",".tau_ledger/receipt.json",".tau_ledger/manifest.json"]
path = next((p for p in CANDIDATES if os.path.exists(p)), None)
if not path: print("FAIL: no manifest/receipt found"); sys.exit(1)
doc = json.load(open(path,"r",encoding="utf-8"))
if doc.get("kind") != "tau-crystal-receipt": print(f"FAIL: wrong kind {doc.get(
"kind")!r}"); sys.exit(1)
payload = json.dumps({k:v for k,v in doc.items() if k not in {"signature","digest"}}, separators=(",",":")).encode("utf-8")
digest = hashlib.sha256(payload).hexdigest()
if "digest" in doc and doc["digest"] != digest: print("FAIL: digest mismatch"); sys.exit(1)
print(f"OK: tau-crystal-receipt verified basic integrity (sha256={digest[:12]}...)")
