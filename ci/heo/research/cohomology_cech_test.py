#!/usr/bin/env python3
import json, subprocess, sys, os

def run(cmd):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if p.returncode != 0:
        print(p.stdout); print(p.stderr, file=sys.stderr); sys.exit(p.returncode)
    return json.loads(p.stdout)

def main():
    ok = True
    # Case A: same sequence → obstruction vanishes
    A = run([
        sys.executable, "ci/heo/research/cohomology_cech.py",
        "--sequence1", "ci/data/sequences/periodic_7_0010010.json",
        "--sequence2", "ci/data/sequences/periodic_7_0010010.json",
        "--d", "2", "--k1", "0", "--k2", "1",
        "--cover-step", "7", "--cover-size", "8"
    ])
    # Case B: different periodic means → obstruction should not vanish
    B = run([
        sys.executable, "ci/heo/research/cohomology_cech.py",
        "--sequence1", "ci/data/sequences/periodic_7_0010010.json",
        "--sequence2", "ci/data/sequences/periodic_5_01010.json",
        "--d", "2", "--k1", "0", "--k2", "1",
        "--cover-step", "5", "--cover-size", "8"
    ])

    summary = {
        "case_A_same_sequence_vanishes": A["obstruction_vanishes"],
        "case_B_diff_sequence_not_vanish": (not B["obstruction_vanishes"]),
        "A_max_abs_delta": A["max_abs_delta"],
        "B_max_abs_delta": B["max_abs_delta"]
    }
    print(json.dumps(summary, indent=2))

    assert A["obstruction_vanishes"] is True, "Čech obstruction should vanish for identical sequences"
    assert B["obstruction_vanishes"] is False, "Čech obstruction should NOT vanish for sequences with different mean"

if __name__ == "__main__":
    main()
