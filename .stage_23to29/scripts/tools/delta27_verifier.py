#!/usr/bin/env python3
import json, sys
def verify_delta27(json_path):
    with open(json_path, "r") as f: data = json.load(f)
    deltas = data.get("delta27", [])
    if not deltas: print("FAIL: no delta27 in %s" % json_path); sys.exit(1)
    valid = all(abs(d) <= 0.01 for d in deltas)
    if valid: print("OK: delta27 valid in %s" % json_path)
    else: print("FAIL: delta27 invalid in %s" % json_path); sys.exit(1)
if __name__ == "__main__":
    if len(sys.argv) != 2: print("Usage: %s <json>" % sys.argv[0]); sys.exit(2)
    verify_delta27(sys.argv[1])
