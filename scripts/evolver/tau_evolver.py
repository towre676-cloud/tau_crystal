#!/usr/bin/env python3
import json, os, random, sys, time
def evolve_params(log_path, out_path):
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    params = {"opt_level": random.choice(["O0", "O1", "O2"]), "cache_size": random.randint(100, 1000)}
    if os.path.exists(log_path):
        with open(log_path, "r") as f: logs = json.load(f)
        if logs: best = min(logs, key=lambda x: x["build_time"])
        params = best["params"] if "params" in best else params
    data = {"schema": "taucrystal/evolver/v1", "id": f"evolver-{time.strftime(\"%Y%m%dT%H%M%SZ\", time.gmtime())}", "params": params}
    with open(out_path, "w") as f: json.dump(data, f, indent=2)
    print(f"[OK] evolved params: {out_path}")
if __name__ == "__main__":
    if len(sys.argv) != 3: print("Usage: %s <log_path> <out_path>" % sys.argv[0]); sys.exit(2)
    evolve_params(sys.argv[1], sys.argv[2])
