#!/usr/bin/env python3
import subprocess, sys, json

BIN = "tools/homotopy/heo_homotopy.py"

def run_json(args):
    out = subprocess.check_output([sys.executable, BIN] + args, text=True)
    return json.loads(out)

def main():
    # Use existing periodic fixture twice (as two reps), expect <=2 components
    args = ["--sequences",
            "ci/data/sequences/periodic_7_0010010.json",
            "ci/data/sequences/periodic_7_0010010.json",
            "--threshold", "10",
            "--compare-len", "2048",
            "--levels", "3"]
    rep = run_json(args)

    # Basic checks
    assert rep["sequence_space"]["num_reps"] == 2, "Expected 2 representatives"
    nc = rep["pi0"]["num_components"]
    assert 1 <= nc <= 2, f"Unexpected component count: {nc}"
    assert "whitehead_tower" in rep and isinstance(rep["whitehead_tower"], dict), "Missing tower"

    # π1 field sanity
    assert "fundamental_group" in rep["pi1"], "Missing π1 summary"

    print(json.dumps({
        "num_reps": rep["sequence_space"]["num_reps"],
        "num_components": nc,
        "pi1": rep["pi1"]["fundamental_group"],
        "levels": list(rep["whitehead_tower"].keys())
    }, indent=2))

if __name__ == "__main__":
    main()
