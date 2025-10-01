#!/usr/bin/env python3
import sys, json
def J(p):
    with open(p, "r", encoding="utf-8") as f:
        return json.load(f)
def check(m1, m2, glued, label):
    h1, h2, T = m1["h"], m2["h"], m1["torsion"]
    if not (T == m2.get("torsion") == glued.get("torsion")):
        print(f"[{label}] torsion mismatch"); sys.exit(2)
    left = (h1 * h2) % T
    right = glued["h"] % T
    ok = (left == right)
    print(f"[{label}] ({h1}*{h2}) %% {T} = {left}; glued={right}; PASS={ok}")
    return ok
def main():
    if len(sys.argv) != 5:
        print("usage: verify_glue.py M1.json M2.json GLUED.json GLUED_BAD.json"); sys.exit(3)
    m1, m2, good, bad = map(J, sys.argv[1:5])
    ok_good = check(m1, m2, good, "glue-ok")
    ok_bad  = check(m1, m2, bad,  "glue-bad")
    if not ok_good:
        print("[glue-ok] FAILED"); sys.exit(1)
    if ok_bad:
        print("[glue-bad] did not fail as expected"); sys.exit(1)
    print("[glue-bad] expected failure observed")
if __name__ == "__main__": main()
