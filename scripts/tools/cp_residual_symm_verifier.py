#!/usr/bin/env python3
import json, sys
def verify_residual_symmetry(json_path):
    with open(json_path, "r") as f: data = json.load(f)
    residuals = data.get("residuals", [])
    if not residuals: print("FAIL: no residuals in %s" % json_path); sys.exit(1)
    symm = all(abs(r) <= 1e-6 for r in residuals)
    if symm: print("OK: residuals symmetric in %s" % json_path)
    else: print("FAIL: residuals not symmetric in %s" % json_path); sys.exit(1)
if __name__ == "__main__":
    if len(sys.argv) != 2: print("Usage: %s <json>" % sys.argv[0]); sys.exit(2)
    verify_residual_symmetry(sys.argv[1])
