#!/usr/bin/env python3
"""Hash verification for tau_crystal certificates (format check; recompute stub)."""
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
            return False, f"Invalid hash format in {U}: {h}"
    return True, "Hash format OK (full verification pending run data)"

def main():
    root = Path(__file__).parent.parent.parent
    examples = root / "certificates" / "examples"
    passed = 0; failed = 0
    for cert_file in sorted(examples.glob("*.json")):
        try:
            cert = json.loads(Path(cert_file).read_text(encoding="utf-8"))
            ok, msg = verify_hashes(cert)
            print(f"[✓] {cert_file.name}: {msg}" if ok else f"[✗] {cert_file.name}: {msg}")
            passed += 1 if ok else 0
            failed += 0 if ok else 1
        except Exception as e:
            print(f"[✗] {cert_file.name}: {e}"); failed += 1
    print(f"\n[summary] passed={passed} failed={failed}")
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
