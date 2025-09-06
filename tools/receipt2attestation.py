#!/usr/bin/env python3
import json, sys, hashlib, time, os

if len(sys.argv) != 2:
    print("usage: receipt2attestation.py out/manifest.json", file=sys.stderr)
    sys.exit(1)

p = sys.argv[1]
b = open(p, "rb").read()
sha = hashlib.sha256(b).hexdigest()
r = json.loads(b.decode("utf-8"))

stmt = {
  "_type": "https://in-toto.io/Statement/v1",
  "subject": [{"name": os.path.basename(p), "digest": {"sha256": sha}}],
  "predicateType": "https://slsa.dev/provenance/v1",
  "predicate": {
    "buildType": "tau-crystal/receipt",
    "metadata": {
      "buildStartedOn": r.get("timestamp_utc"),
      "reproducible": True
    },
    "invocation": {
      "environment": {
        "component": r.get("component"),
        "toolchain": r.get("toolchain"),
        "hardware": r.get("hardware"),
        "equivalence_level": r.get("equivalence_level"),
        "clock": r.get("clock"),
        "context_sha256": (r.get("context") or {}).get("sha256")
      }
    },
    "materials": [
      {"uri": "git:"+r.get("commit_hash",""), "digest": {}}
    ]
  }
}
print(json.dumps(stmt, separators=(",",":")))
