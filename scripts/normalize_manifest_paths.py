#!/usr/bin/env python3
import json, re, sys
from pathlib import Path

REPO = Path.cwd()
MJ   = REPO/"tau-crystal-manifest.json"

def to_posix_rel(s: str) -> str:
    m = re.search(r'([\\/])docs([\\/].*)$', s)
    if m:
        return ("docs" + m.group(2)).replace("\\", "/")
    return s.replace("\\","/")

if not MJ.exists():
    print("[info] no manifest to normalize"); sys.exit(0)

man = json.loads(MJ.read_text(encoding="utf-8"))
changed = False

for e in man.get("included_files", []):
    p0 = e.get("path","")
    p1 = to_posix_rel(p0)
    if p1 != p0:
        e["path"] = p1; changed = True

for a in man.get("archives", []):
    p0 = a.get("path","")
    p1 = to_posix_rel(p0)
    if p1 != p0:
        a["path"] = p1; changed = True

if changed:
    MJ.write_text(json.dumps(man, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("[fixed] normalized manifest paths to POSIX docs/*")
else:
    print("[ok] manifest paths already POSIX/relative")
