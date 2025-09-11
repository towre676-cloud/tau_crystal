#!/usr/bin/env python3
import sys, json, pathlib
rec = pathlib.Path(sys.argv[1]); contract = sys.argv[2]
obj = json.loads(rec.read_text(encoding="utf-8"))
obj["contract_path"] = contract
rec.write_text(json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True), encoding="utf-8")
