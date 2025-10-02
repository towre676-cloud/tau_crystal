#!/usr/bin/env python3
"""
Algebraic Relation Discovery Engine (dependency-light)

Design:
- Treat each sequence JSON as an "observable" X_S(n) over {0,1}.
- Build a proxy grid H_{d}(k) by residue-class or window averages of X_S.
- Discover robust, low-variance relations:
    * equalities H_d(k) == H_d(k')
    * periodicity in k
    * cross-d equality H_{d1}(k) == H_{d2}(k') (when numerically identical)

Notes:
- This miner is *empirical*; it writes τ-Crystal "Conjecture" receipts
  into receipts/heo/discovered/, marked verification.mode="Optional".
- No external libs; works on periodic/explicit fixtures.
"""
import argparse, json, glob, os, math
from statistics import mean

# ---------- helpers ----------
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
    """Density over indices n ≡ residue (mod modulus), 1-indexed."""
    T = len(pattern)
    # in periodic model, X(n) depends only on n mod T; density on a residue class
    # modulo T is just the pattern value at that class.
    r = (residue - 1) % T
    return float(pattern[r])

def window_avg(values, start, width):
    N = len(values)
    if N == 0: return 0.0
    acc = 0
    for i in range(width):
        acc += values[(start + i) % N]
    return acc / width

def build_H_grid(seq, ds=(2,3,5), max_k=12):
    """
    Construct H-values for (d,k).
    Strategy:
      - If periodic: use residue-class density mod T for k=1..min(T, max_k).
      - If explicit: use sliding-window averages (width = min(32, N)).
    """
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

def almost_equal(a, b, tol=1e-9):
    return abs(a-b) <= tol

# ---------- relation mining ----------
def discover_equalities(H_grid):
    """Find pairs (k,k') with H_d(k) == H_d(k')."""
    relations = []
    # group by fixed d
    by_d = {}
    for (d,k), h in H_grid.items():
        by_d.setdefault(d, []).append((k, h))
    for d, items in by_d.items():
        items.sort()
        for i in range(len(items)):
            k_i, h_i = items[i]
            for j in range(i+1, len(items)):
                k_j, h_j = items[j]
                if almost_equal(h_i, h_j):
                    relations.append({
                        "type": "equality_in_k",
                        "d": d,
                        "k": k_i,
                        "k_prime": k_j,
                        "value": h_i,
                        "confidence": 0.99
                    })
    return relations

def discover_periodicity(H_grid, max_period=12):
    """Detect minimal period p in k for each fixed d (if any)."""
    relations = []
    by_d = {}
    for (d,k), h in H_grid.items():
        by_d.setdefault(d, []).append((k, h))
    for d, items in by_d.items():
        items.sort()
        ks = [k for k,_ in items]
        hs = [h for _,h in items]
        L = len(hs)
        if L < 2: 
            continue
        for p in range(1, min(max_period, L)+1):
            ok = True
            for i in range(L):
                if not almost_equal(hs[i], hs[(i+p)%L]):
                    ok = False; break
            if ok:
                relations.append({
                    "type": "periodicity",
                    "d": d,
                    "period": p,
                    "confidence": 0.95
                })
                break
    return relations

def discover_cross_degree_equalities(H_grid):
    """Find (d1,k1) and (d2,k2) with the same value."""
    relations = []
    items = list(H_grid.items())  # [((d,k), h)]
    for i in range(len(items)):
        (d1,k1), h1 = items[i]
        for j in range(i+1, len(items)):
            (d2,k2), h2 = items[j]
            if d1 == d2: 
                continue
            if almost_equal(h1, h2):
                relations.append({
                    "type": "cross_degree_equality",
                    "d1": d1, "k1": k1,
                    "d2": d2, "k2": k2,
                    "value": h1,
                    "confidence": 0.9
                })
    return relations

# ---------- receipts ----------
def generate_latex_statement(rel, seq_label):
    t = rel["type"]
    if t == "equality_in_k":
        d = rel["d"]; k = rel["k"]; k2 = rel["k_prime"]
        return (f"For sequence {seq_label}, "
                f"\\(\\mathbf{{H}}_{{{d}}}^S({k}) = "
                f"\\mathbf{{H}}_{{{d}}}^S({k2})\\).")
    if t == "periodicity":
        d = rel["d"]; p = rel["period"]
        return (f"For sequence {seq_label}, \\(\\mathbf{{H}}_{{{d}}}^S(k)\\) "
                f"is periodic in \\(k\\) with period \\({p}\\).")
    if t == "cross_degree_equality":
        d1 = rel["d1"]; k1 = rel["k1"]; d2 = rel["d2"]; k2 = rel["k2"]
        return (f"For sequence {seq_label}, "
                f"\\(\\mathbf{{H}}_{{{d1}}}^S({k1}) = "
                f"\\mathbf{{H}}_{{{d2}}}^S({k2})\\).")
    return "Empirical relation"

def emit_receipts(seq_path, seq_label, relations, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    out_files = []
    for i, rel in enumerate(relations):
        rid = f"{os.path.splitext(os.path.basename(seq_path))[0]}_{rel['type']}_{i}"
        receipt = {
            "id": f"heo.discovered.{rid}",
            "type": "Conjecture",
            "title": f"Discovered relation: {rel['type']} ({seq_label})",
            "tier": 10,
            "statement_md": generate_latex_statement(rel, seq_label),
            "proof_status": "Empirical",
            "evidence": [f"auto-mined from {seq_path}"],
            "verification": {
                "mode": "Optional",
                "tests": [{
                    "name": f"verify_{rel['type']}",
                    "script": "ci/heo/research/verify_relation.py",
                    "args": ["--relation-json", f"receipts/heo/discovered/{rid}.json"],
                    "expect": {"status": "pass"}
                }]
            },
            "metadata": rel
        }
        out_file = os.path.join(out_dir, f"{rid}.json")
        with open(out_file, "w") as f:
            json.dump(receipt, f, indent=2)
        out_files.append(out_file)
    return out_files

# ---------- CLI ----------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequences-glob", default="ci/data/sequences/*.json")
    ap.add_argument("--out-dir", default="receipts/heo/discovered")
    ap.add_argument("--ds", default="2,3,5")
    ap.add_argument("--max-k", type=int, default=16)
    args = ap.parse_args()

    ds = tuple(int(x) for x in args.ds.split(",") if x.strip())
    seq_paths = sorted(glob.glob(args.sequences_glob))
    all_receipts = []

    for path in seq_paths:
        try:
            seq = load_sequence(path)
        except Exception as e:
            print(json.dumps({"warning":"skip", "path":path, "error":str(e)}))
            continue

        label = os.path.splitext(os.path.basename(path))[0]
        H = build_H_grid(seq, ds=ds, max_k=args.max_k)

        rels = []
        rels += discover_equalities(H)
        rels += discover_periodicity(H)
        rels += discover_cross_degree_equalities(H)

        out_files = emit_receipts(path, label, rels, args.out_dir)
        all_receipts.extend(out_files)

    print(json.dumps({
        "status":"ok",
        "sequences_seen": len(seq_paths),
        "receipts_emitted": len(all_receipts),
        "out_dir": args.out_dir
    }, indent=2))

if __name__ == "__main__":
    main()
