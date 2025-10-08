#!/usr/bin/env python
import json, sys
out = {
  "status": "stub",
  "order": 4,
  "verified": ["a4","a5"],
  "note": "replace with MDE inference/verification"
}
print(json.dumps(out))
