#!/usr/bin/env python3
import sys, json
label = sys.argv[1] if len(sys.argv)>1 else "11a1"
path  = sys.argv[2] if len(sys.argv)>2 else "analysis/atlas/atlas_hecke.jsonl"
line = None
try:
  with open(path, "r", encoding="utf-8", errors="replace") as f:
    for L in f:
      if "\"label\":\"%s\"" % label in L:
        line = L; break
except FileNotFoundError:
  pass
if not line:
  print("NA NA NA NA NA"); sys.exit(1)
d = json.loads(line)
a = d.get("a") or d.get("coeffs") or {}
print(a.get("a1","NA"), a.get("a2","NA"), a.get("a3","NA"), a.get("a4","NA"), a.get("a6","NA"))
