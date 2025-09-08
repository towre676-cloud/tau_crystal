#!/usr/bin/env python3
import json, os, sys
root = os.path.abspath(sys.argv[1] if len(sys.argv)>1 else ".")
mf = os.path.join(root, "lake-manifest.json")
with open(mf, "r", encoding="utf-8") as f:
  doc = json.load(f)
sha = None
for p in doc.get("packages", []):
  n = p.get("name") or (p.get("package") or {}).get("name")
  if n and (n.lower().startswith("mathlib") or n == "mathlib"):
    src = p.get("src", {})
    sha = src.get("rev") or src.get("revId") or src.get("hash")
    break
if not sha:
  raise SystemExit("mathlib rev not found in lake-manifest.json")
print(sha)
