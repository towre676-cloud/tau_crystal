#!/usr/bin/env python3
"""Hash verification for tau_crystal certificates (ASCII-only output)."""
import json, hashlib, sys
from pathlib import Path

def canonical_json(obj):
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(',', ': '), allow_nan=False) + '\n'

def compute_hash(data_str):
    return "sha256:" + hashlib.sha256(data_str.encode('utf-8')).hexdigest()[:8] + "..."

def verify_hashes(cert):
    if "descent_certificate" not in cert:
        return True, "No restrictions to verify"
    restrictions = cert["descent_certificate"]["restrictions"]
    for U, v in restrictions.items():
        h = v.get("hash", "")
        if not isinstance(h, str) or not h.startswith("sha256:"):
            return False, "Invalid hash format in %s: %s" % (U, h)
    return True, "Hash format OK (full verification pending run data)"

def main():
    root = Path(__file__).parent.parent.parent
    examples = root / "certificates" / "examples"
    passed = 0; failed = 0
    for cert_file in sorted(examples.glob("*.json")):
        try:
            cert = json.loads(Path(cert_file).read_text(encoding="utf-8"))
            ok, msg = verify_hashes(cert)
            if ok:
                print("[OK]   %s: %s" % (cert_file.name, msg)); passed += 1
            else:
                print("[FAIL] %s: %s" % (cert_file.name, msg)); failed += 1
        except Exception as e:
            print("[FAIL] %s: %s" % (cert_file.name, e)); failed += 1
    print("\n[summary] passed=%d failed=%d" % (passed, failed))
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
