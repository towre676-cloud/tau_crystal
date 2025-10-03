#!/usr/bin/env python3
import json,sys
data=json.load(sys.stdin)
sys.stdout.write(json.dumps(data, sort_keys=True, separators=(",",":")))
