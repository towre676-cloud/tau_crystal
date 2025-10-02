#!/usr/bin/env python3
"""
Verify a discovered HEO relation by re-computing the H-grid
from the originating sequence fixture.

Usage:
  python ci/heo/research/verify_relation.py \
    --relation-json receipts/heo/discovered/<rid>.json

The <rid> is of the form: <seq_basename>_<type>_<index>
We reconstruct the sequence path as: ci/data/sequences/<seq_basename>.json
"""
import argparse, json, os, math, sys

TOL = 1e-9

def fail(msg, extra=None):
    out = {"status":"fail", "reason": msg}
    if extra: out.update(extra)
    print(json.dumps(out, indent=2))
    sys.exit(1)

def ok(payload):
    payload.setdefault("status", "pass")
    print(json.dumps(payload, indent=2))
    sys.exit(0)

def load_sequence(path):
    with open(path, "r") as f:
        obj = json.load(f)
    kind = obj.get("kind", "periodic")
    if kind == "periodic":
        patt = obj["pattern"]
        assert all(x in (0,1) for x in patt), "pattern must be 0/1"
        return {"kind":"periodic", "pattern": patt, "period": len(patt)}
    elif kind == "explicit":
        vals = obj["values"]
        return {"kind":"explicit", "values": vals, "period": len(vals)}
    else:
        raise ValueError(f"unsupported kind: {kind}")

def residue_density_periodic(pattern, residue, modulus):
    r = (residue - 1) % len(pattern)
    return float(pattern[r])

def window_avg(values, start, width):
    N = len(values)
    if N == 0: return 0.0
    acc = 0
    for i in range(width):
        acc += values[(start + i) % N]
    return acc / width

def build_H_grid(seq, ds=(2,3,5), max_k=64):
    H = {}
    if seq["kind"] == "periodic":
        patt = seq["pattern"]
        T = len(patt)
        K = min(T, max_k)
        for d in ds:
            for k in range(1, K+1):
                H[(d, k)] = residue_density_periodic(patt, k, T)
    else:
        vals = seq["values"]
        N = len(vals)
        W = max(1, min(32, N))
        K = min(N, max_k)
        for d in ds:
            for k in range(0, K):
                H[(d, k+1)] = window_avg(vals, k, W)
    return H

def almost_equal(a, b, tol=TOL):
    return abs(a - b) <= tol

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--relation-json", required=True)
    ap.add_argument("--seq-dir", default="ci/data/sequences")
    args = ap.parse_args()

    # Load relation receipt
    with open(args.relation_json, "r") as f:
        receipt = json.load(f)

    rid = receipt["id"].split(".")[-1]  # heo.discovered.<rid>
    # rid format: <seq_basename>_<type>_<idx>
    # robustly split from right to get basename
    parts = rid.rsplit("_", 2)
    if len(parts) < 3:
        fail("bad_rid_format", {"rid": rid})
    seq_basename = parts[0]
    rel_type = receipt.get("metadata", {}).get("type", parts[1])

    seq_path = os.path.join(args.seq_dir, f"{seq_basename}.json")
    if not os.path.exists(seq_path):
        fail("sequence_not_found", {"seq_path": seq_path})

    seq = load_sequence(seq_path)
    H = build_H_grid(seq, ds=(2,3,5), max_k=128)

    rel = receipt.get("metadata", {})
    verdict = {"relation_type": rel_type, "seq": seq_basename, "tolerance": TOL}

    if rel_type == "equality_in_k":
        d = int(rel["d"]); k = int(rel["k"]); kp = int(rel["k_prime"])
        h1 = H.get((d,k)); h2 = H.get((d,kp))
        if h1 is None or h2 is None:
            fail("missing_H_values", {"d": d, "k": k, "k'": kp})
        if not almost_equal(h1, h2):
            fail("not_equal", {"d": d, "k": k, "k'": kp, "Hk": h1, "Hk'": h2})
        verdict.update({"d": d, "k": k, "k'": kp, "H": h1})

    elif rel_type == "periodicity":
        d = int(rel["d"]); p = int(rel["period"])
        # Collect ks present for this d
        ks = sorted(k for (dd,k) in H.keys() if dd == d)
        if not ks:
            fail("no_k_values_for_d", {"d": d})
        # Check k ~ k+p
        ok_all = True
        bad = []
        for k in ks:
            if (d, k) in H and (d, k+p) in H:
                if not almost_equal(H[(d,k)], H[(d,k+p)]):
                    ok_all = False
                    bad.append({"k": k, "Hk": H[(d,k)], "Hk+p": H[(d,k+p)]})
        if not ok_all:
            fail("periodicity_violation", {"d": d, "period": p, "violations": bad[:5]})
        verdict.update({"d": d, "period": p, "checked_count": len(ks)})

    elif rel_type == "cross_degree_equality":
        d1 = int(rel["d1"]); k1 = int(rel["k1"])
        d2 = int(rel["d2"]); k2 = int(rel["k2"])
        h1 = H.get((d1,k1)); h2 = H.get((d2,k2))
        if h1 is None or h2 is None:
            fail("missing_H_values", {"(d1,k1)": [d1,k1], "(d2,k2)": [d2,k2]})
        if not almost_equal(h1, h2):
            fail("not_equal_cross_degree",
                 {"(d1,k1)": [d1,k1], "H1": h1, "(d2,k2)": [d2,k2], "H2": h2})
        verdict.update({"d1": d1, "k1": k1, "d2": d2, "k2": k2, "H": h1})

    else:
        fail("unknown_relation_type", {"type": rel_type})

    ok(verdict)

if __name__ == "__main__":
    main()
