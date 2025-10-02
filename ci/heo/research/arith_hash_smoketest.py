#!/usr/bin/env python3
import subprocess, json, sys, os, tempfile, binascii

BIN = "tools/crypto/arith_hash.py"

def run_json(args):
    out = subprocess.check_output([sys.executable, BIN] + args, text=True)
    return json.loads(out)

def main():
    # Determinism for same message
    r1 = run_json(["--message", "Hello, HEO!"])
    r2 = run_json(["--message", "Hello, HEO!"])
    assert r1["hash_hex"] == r2["hash_hex"], "Non-deterministic hash"

    # Distinct messages → likely distinct hashes (not guaranteed, but check trivial case)
    r3 = run_json(["--message", "Hello, HEO?."])
    assert r1["hash_hex"] != r3["hash_hex"], "Unexpected collision on trivial variant"

    # Avalanche test basic sanity
    ra = run_json(["--message", "Hello, HEO!", "--test-avalanche", "--flips", "8"])
    avg = ra.get("average_hamming", 0.0)
    # Accept fairly weak bound to avoid flakiness; must be > 32 bits on average
    assert avg > 32.0, f"Avalanche too weak: {avg}"

    print(json.dumps({
        "determinism_ok": True,
        "trivial_collision_check": True,
        "avg_hamming": avg,
        "base_hash": ra.get("base_hash")
    }, indent=2))
    sys.exit(0)

if __name__ == "__main__":
    main()
