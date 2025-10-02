#!/usr/bin/env python3
import glob, json, os
paths = glob.glob("receipts/heo/**/**/*.json", recursive=True)
summary = []
for p in sorted(paths):
    try:
        obj = json.load(open(p))
        summary.append({"id": obj.get("id"), "type": obj.get("type"), "tier": obj.get("tier"), "path": p})
    except Exception as e:
        summary.append({"id": None, "type": "Invalid", "tier": None, "path": p, "error": str(e)})
print(json.dumps({"count": len(summary), "items": summary}, indent=2))
