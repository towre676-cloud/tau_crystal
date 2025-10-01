#!/usr/bin/env python3
import sys, json, io, os
dec = json.JSONDecoder()
def sanitize(path):
    with open(path,'rb') as f:
        b = f.read()
    s = b.decode('utf-8', 'replace')
    try:
        obj, end = dec.raw_decode(s)
    except Exception as e:
        print(f"[sanitize] parse fail: {path}: {e}", file=sys.stderr)
        return 1
    rest = s[end:].strip()
    if rest:
        # trailing junk present; trim
        pass
    # dump back as JCS-ish compact form
    out = json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",",":"))
    with open(path,'wb') as f:
        f.write(out.encode('utf-8'))
    return 0
rc = 0
for p in sys.argv[1:]:
    rc |= sanitize(p)
sys.exit(rc)
