#!/usr/bin/env python3
from fastapi.testclient import TestClient
import json, sys
from tools.dashboard.backend.main import app

client = TestClient(app)

# Fixture pattern: periodic 0010010 (period 7)
pattern = [0,0,1,0,0,1,0]

r1 = client.post("/compute_heo", json={"pattern": pattern, "d": 2, "k": 0})
assert r1.status_code == 200, r1.text
out1 = r1.json()
assert abs(out1["H"] - (sum(pattern)/len(pattern))) < 1e-12

r2 = client.post("/compute_spectrum", json={"pattern": pattern, "k_min": -3, "k_max": 3, "ds": [2,3]})
assert r2.status_code == 200, r2.text
out2 = r2.json()
assert len(out2["heatmap"]) == (3 - (-3) + 1) * 2  # 7 ks * 2 ds

print(json.dumps({"compute_heo": out1, "compute_spectrum": out2}, indent=2))
sys.exit(0)
