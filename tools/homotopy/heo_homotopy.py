#!/usr/bin/env python3
"""
HEO Sequence-Space: finite-surgery equivalence, π0/π1 approximations,
and a Whitehead-tower-style filtration.

Input: one or more sequence JSON files (periodic/explicit fixtures).
Output: JSON summary of components, loops, and tower.

Example:
  python tools/homotopy/heo_homotopy.py \
    --sequences ci/data/sequences/periodic_7_0010010.json
"""
from __future__ import annotations
import argparse, json, math, sys
from typing import Dict, List, Any
from dataclasses import dataclass

@dataclass
class Rep:
    label: str
    data: Dict[str, Any]  # expects {"kind": "...", "pattern": [...] } or {"values": [...]}

def _load_sequence(path: str) -> Dict[str, Any]:
    with open(path, "r") as f:
        return json.load(f)

def _materialize_pattern(obj: Dict[str, Any], min_len: int = 0) -> List[int]:
    """
    Return a (possibly periodic) 0/1 pattern materialized to at least min_len length if periodic.
    Falls back to explicit values if 'pattern' not present.
    """
    if obj.get("kind") == "periodic" and "pattern" in obj:
        patt = list(map(int, obj["pattern"]))
        if min_len <= 0:
            return patt
        q = (min_len + len(patt) - 1) // len(patt)
        return (patt * q)[:min_len]
    if obj.get("kind") == "explicit" and "values" in obj:
        return list(map(int, obj["values"]))
    # best-effort fallback
    if "pattern" in obj:
        return list(map(int, obj["pattern"]))
    if "values" in obj:
        return list(map(int, obj["values"]))
    raise ValueError("Unrecognized sequence format")

def _density_from_pattern(patt: List[int]) -> float:
    if not patt:
        return 0.0
    return sum(1 if x else 0 for x in patt) / len(patt)

class SequenceSpace:
    """
    Topological model (combinatorial) for HEO sequences.
    - Representatives are sequences (0/1 indicator patterns).
    - Finite-surgery equivalence: differ on ≤ threshold entries (after aligning lengths).
    """
    def __init__(self, threshold: int = 10, compare_len: int = 4096):
        self.reps: List[Rep] = []
        self.threshold = int(threshold)
        self.compare_len = int(compare_len)

    def add(self, label: str, data: Dict[str, Any]) -> None:
        self.reps.append(Rep(label=label, data=data))

    def finite_surgery_equivalent(self, A: Rep, B: Rep) -> bool:
        # materialize to same length
        LA = _materialize_pattern(A.data, self.compare_len)
        LB = _materialize_pattern(B.data, self.compare_len)
        L = max(len(LA), len(LB), self.compare_len)
        if len(LA) < L: LA = (LA * ((L + len(LA) - 1)//len(LA)))[:L]
        if len(LB) < L: LB = (LB * ((L + len(LB) - 1)//len(LB)))[:L]
        diff = sum(1 for a, b in zip(LA, LB) if a != b)
        return diff <= self.threshold

    def components_pi0(self) -> Dict[str, Any]:
        """
        Connected components under finite-surgery equivalence.
        Greedy union-find by scanning pairs (sufficient for small rep sets).
        """
        n = len(self.reps)
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra

        for i in range(n):
            for j in range(i+1, n):
                if self.finite_surgery_equivalent(self.reps[i], self.reps[j]):
                    union(i, j)

        comps: Dict[int, List[int]] = {}
        for i in range(n):
            r = find(i)
            comps.setdefault(r, []).append(i)

        out = []
        for r, idxs in comps.items():
            out.append({
                "representative": self.reps[r].label,
                "size": len(idxs),
                "members": [self.reps[k].label for k in idxs]
            })
        return {
            "num_components": len(out),
            "components": out
        }

    def fundamental_group_pi1(self, base_idx: int = 0) -> Dict[str, Any]:
        """
        π1 approximation: loops via two-step finite surgeries returning to base.
        We report trivial/non-trivial based on existence of distinct intermediate
        reps reachable from and returning to base (still an abstract diagnostic).
        """
        if not self.reps:
            return {"basepoint": None, "num_loops": 0, "loops": [], "fundamental_group": "trivial"}
        base = self.reps[min(base_idx, len(self.reps)-1)]
        loops = []
        for i, inter in enumerate(self.reps):
            if i == base_idx: 
                continue
            if self.finite_surgery_equivalent(base, inter) and self.finite_surgery_equivalent(inter, base):
                loops.append({"via": inter.label})
        fg = "non-trivial" if loops else "trivial"
        return {
            "basepoint": base.label,
            "num_loops": len(loops),
            "loops": loops,
            "fundamental_group": fg
        }

    def whitehead_tower(self, levels: int = 3) -> Dict[str, Any]:
        """
        Filtration by 'connectivity' proxy: # of non-zero densities over a small k-grid.
        Here we approximate with global density thresholding.
        """
        # Precompute a density per rep (from one period/values)
        rep_dens: Dict[str, float] = {}
        for rep in self.reps:
            patt = _materialize_pattern(rep.data, 0)
            rep_dens[rep.label] = _density_from_pattern(patt)

        tower = {}
        # Level 1: allow density > 0 (non-empty), Level 0: density == 0
        # For demonstration, define simple cutoffs:
        #   level 1: H == 0
        #   level 2: 0 < H <= 1/2
        #   level 3: H > 1/2
        for lev in range(1, levels+1):
            if lev == 1:
                elig = [r.label for r in self.reps if rep_dens[r.label] == 0.0]
            elif lev == 2:
                elig = [r.label for r in self.reps if 0.0 < rep_dens[r.label] <= 0.5]
            else:
                elig = [r.label for r in self.reps if rep_dens[r.label] > 0.5]
            tower[lev] = {
                "connectivity": lev,
                "eligible_count": len(elig),
                "sequences": elig
            }
        return tower

def cli():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequences", nargs="+", required=True, help="Paths to JSON sequence fixtures")
    ap.add_argument("--threshold", type=int, default=10, help="Finite-surgery difference threshold")
    ap.add_argument("--compare-len", type=int, default=4096, help="Length to compare after periodic expansion")
    ap.add_argument("--levels", type=int, default=3, help="Whitehead tower levels to compute")
    args = ap.parse_args()

    space = SequenceSpace(threshold=args.threshold, compare_len=args.compare_len)
    for i, path in enumerate(args.sequences):
        obj = _load_sequence(path)
        space.add(label=f"S{i}:{path}", data=obj)

    pi0 = space.components_pi0()
    pi1 = space.fundamental_group_pi1(base_idx=0)
    tower = space.whitehead_tower(levels=args.levels)

    out = {
        "sequence_space": {
            "num_reps": len(space.reps),
            "threshold": args.threshold,
            "compare_len": args.compare_len
        },
        "pi0": pi0,
        "pi1": pi1,
        "whitehead_tower": tower
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    cli()
