#!/usr/bin/env python3
import json,sys; p=(sys.argv[1] if len(sys.argv)>1 else ".")+"/lake-manifest.json"; j=json.load(open(p,"r",encoding="utf-8"))
for d in j.get("packages",[]):
  if d.get("name")=="mathlib": print(d.get("rev") or d.get("git") or "unknown"); sys.exit(0)
print("unknown")
