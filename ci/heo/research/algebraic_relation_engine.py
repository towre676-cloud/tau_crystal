#!/usr/bin/env python3
"""
Algebraic Relation Discovery Engine (stable IDs + index emission)

Discovers simple algebraic relations among HEO values computed from sequence fixtures,
then emits machine-readable receipts in receipts/heo/discovered/ with stable IDs:

  id = "heo.discovered.<seq_basename>_<type>_<index>"

Supported relation types:
  - equality_in_k        : H_d(k) == H_d(k') for selected pairs
  - periodicity          : H_d(k) == H_d(k + p) for detected period p
  - cross_degree_equality: H_{d1}(k1) == H_{d2}(k2)

All receipts are Conjecture/Empirical and non-blocking in CI.
"""
import argparse, glob, json, math, os, re, sys
from collections import defaultdict
from fractions import Fraction

TOL = 1e-9

def seq_basename_from_path(path: str) -> str:
    base = os.path.basename(path)
    if base.lower().endswith(".json"):
        base = base[:-5]
    # normalize: keep alnum + _ only
    return re.sub(r'[^A-Za-z0-9_]+', '_', base)

def load_sequence(path):
    with open(path, "r") as f:
        obj = json.load(f)
    kind = obj.get("kind", "periodic")
    if kind == "periodic":
        patt = obj["pattern"]
        if not patt: raise ValueError("empty periodic pattern")
        return {"kind":"periodic","pattern":patt,"period":len(patt)}
    elif kind == "explicit":
        vals = obj["values"]
        if not vals: raise ValueError("empty explicit values")
        return {"kind":"explicit","values":vals,"period":len(vals)}
    else:
        raise ValueError(f"unsupported kind: {kind}")

def residue_density_periodic(pattern, k):
    # Indexing: positions 1..T map to residues 0..T-1
    T = len(pattern)
    r = (k - 1) % T
    return float(pattern[r])

def window_avg(values, start, width):
    N = len(values)
    if N == 0: return 0.0
    acc = 0
    for i in range(width):
        acc += values[(start + i) % N]
    return acc / width

def compute_H_grid(seq, ds, max_k=64):
    H = {}
    if seq["kind"] == "periodic":
        patt = seq["pattern"]
        T = len(patt)
        K = min(T, max_k if max_k>0 else T)
        for d in ds:
            for k in range(1, K+1):
                H[(d,k)] = residue_density_periodic(patt, k)
    else:
        vals = seq["values"]
        N = len(vals)
        W = max(1, min(32, N))
        K = min(N, max_k if max_k>0 else N)
        for d in ds:
            for k in range(1, K+1):
                H[(d,k)] = window_avg(vals, k-1, W)
    return H

def almost_equal(a, b, tol=TOL):
    return abs(a - b) <= tol

def discover_relations_for_sequence(seq, ds, max_k):
    H = compute_H_grid(seq, ds, max_k)
    rels = []

    # 1) equality_in_k per fixed d: scan pairs (k,k')
    by_d = defaultdict(list)
    for (d,k), h in H.items():
        by_d[d].append((k,h))
    for d, arr in by_d.items():
        arr.sort()
        n = len(arr)
        # simple n^2 scan for small k-range
        for i in range(n):
            k, h = arr[i]
            for j in range(i+1, n):
                kp, hp = arr[j]
                if almost_equal(h, hp):
                    rels.append({
                        "type":"equality_in_k",
                        "d": int(d),
                        "k": int(k),
                        "k_prime": int(kp),
                        "H": h
                    })

    # 2) periodicity guess: check smallest p s.t. many equalities hold
    for d, arr in by_d.items():
        ks = [k for (k,_) in arr]
        if not ks: continue
        Kmax = max(ks)
        T_candidates = list(range(1, min(16, Kmax)+1))
        for p in T_candidates:
            ok = True
            checks = 0
            for (k,h) in arr:
                k2 = k + p
                if (d,k2) in H:
                    checks += 1
                    if not almost_equal(h, H[(d,k2)]):
                        ok = False
                        break
            if ok and checks >= max(3, Kmax//3):
                rels.append({
                    "type":"periodicity",
                    "d": int(d),
                    "period": int(p),
                    "evidence_checks": int(checks)
                })
                break  # record the smallest p

    # 3) cross_degree_equality: align ks where both present
    ds_sorted = sorted(set(d for (d,_) in H.keys()))
    for i in range(len(ds_sorted)):
        for j in range(i+1, len(ds_sorted)):
            d1, d2 = ds_sorted[i], ds_sorted[j]
            for k in range(1, max_k+1):
                if (d1,k) in H and (d2,k) in H and almost_equal(H[(d1,k)], H[(d2,k)]):
                    rels.append({
                        "type":"cross_degree_equality",
                        "d1": int(d1), "k1": int(k),
                        "d2": int(d2), "k2": int(k),
                        "H": H[(d1,k)]
                    })
    return rels

def latex_statement(rel, seq_name):
    t = rel["type"]
    if t == "equality_in_k":
        d,k,kp = rel["d"], rel["k"], rel["k_prime"]
        return (f"For sequence {seq_name}, "
                f"\\(\\mathbf{{H}}_{{{d}}}^S({k}) = \\mathbf{{H}}_{{{d}}}^S({kp})\\).")
    if t == "periodicity":
        d,p = rel["d"], rel["period"]
        return (f"For sequence {seq_name}, "
                f"\\(\\mathbf{{H}}_{{{d}}}^S(k) = \\mathbf{{H}}_{{{d}}}^S(k + {p})\\) for all admissible \\(k\\).")
    if t == "cross_degree_equality":
        d1,k1,d2,k2 = rel["d1"], rel["k1"], rel["d2"], rel["k2"]
        return (f"For sequence {seq_name}, "
                f"\\(\\mathbf{{H}}_{{{d1}}}^S({k1}) = \\mathbf{{H}}_{{{d2}}}^S({k2})\\).")
    return "Unspecified relation."

def emit_receipts(relations, out_dir, seq_basename):
    os.makedirs(out_dir, exist_ok=True)
    emitted = []
    counters = defaultdict(int)
    for rel in relations:
        rtype = rel["type"]
        counters[rtype] += 1
        rid_local = f"{seq_basename}_{rtype}_{counters[rtype]}"
        rid_full  = f"heo.discovered.{rid_local}"
        receipt = {
            "id": rid_full,
            "type": "Conjecture",
            "title": f"Discovered relation ({rtype}) on {seq_basename}",
            "tier": 10,
            "statement_md": latex_statement(rel, seq_basename),
            "proof_status": "Empirical",
            "verification": {
                "mode": "Optional",
                "tests": [{
                    "name": f"verify_{rtype}",
                    "script": "ci/heo/research/verify_relation.py",
                    "args": ["--relation-json", f"receipts/heo/discovered/{rid_local}.json"],
                    "expect": {"status": "pass"}
                }]
            },
            "metadata": {"type": rtype, **rel, "seq_basename": seq_basename}
        }
        path = os.path.join(out_dir, f"{rid_local}.json")
        with open(path, "w") as f:
            json.dump(receipt, f, indent=2)
        emitted.append({"id": rid_full, "path": path, "type": rtype})
    return emitted

def write_index(index_path, entries):
    with open(index_path, "w") as f:
        json.dump({"relations": entries}, f, indent=2)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequences-glob", default="ci/data/sequences/*.json")
    ap.add_argument("--out-dir", default="receipts/heo/discovered")
    ap.add_argument("--ds", default="2,3,5")
    ap.add_argument("--max-k", type=int, default=16)
    args = ap.parse_args()

    ds = tuple(int(x) for x in args.ds.split(",") if x.strip())
    entries = []
    for spath in sorted(glob.glob(args.sequences_glob)):
        try:
            seq = load_sequence(spath)
        except Exception as e:
            print(f"[skip] {spath}: {e}", file=sys.stderr); continue
        seq_name = seq_basename_from_path(spath)
        rels = discover_relations_for_sequence(seq, ds, args.max_k)
        emitted = emit_receipts(rels, args.out_dir, seq_name)
        entries.extend(emitted)

    write_index(os.path.join(args.out_dir, "index.json"), entries)
    print(json.dumps({"emitted": len(entries), "out_dir": args.out_dir}, indent=2))

if __name__ == "__main__":
    main()
