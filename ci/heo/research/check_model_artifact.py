#!/usr/bin/env python3
import json, argparse, sys
REQ = ["train_mae","test_mae","dof","lambda","columns","weights"]
ap = argparse.ArgumentParser()
ap.add_argument("--model", required=True)
args = ap.parse_args()
obj = json.load(open(args.model))
missing = [k for k in REQ if k not in obj]
assert not missing, f"missing keys: {missing}"
assert isinstance(obj["columns"], list) and isinstance(obj["weights"], list), "columns/weights must be lists"
assert len(obj["weights"]) == len(obj["columns"]) + 1, "weights must match 1+bias+len(columns)"
print(json.dumps({"ok": True, "model_keys": list(obj.keys())}, indent=2))
