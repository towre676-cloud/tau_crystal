#!/usr/bin/env python3
import sys, json, pathlib
p = pathlib.Path(sys.argv[1])
with p.open("rb") as f: obj = json.load(f)
s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
sys.stdout.write(s)
