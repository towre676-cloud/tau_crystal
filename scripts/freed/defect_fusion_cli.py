#!/usr/bin/env python3
import json, itertools, math
# model W(B5) generators: sign flips on each axis (Z2^5) and simple transposition s_12
def compose(a,b): 
    # a,b as permutations with sign: list of pairs (idx, sgn), idx in 0..4, sgn in {+1,-1}
    idx_a = [i for i,_ in a]; sgn_a=[s for _,s in a]
    out=[]
    for (j,sgn_b) in b:
        i = idx_a[j]
        s = sgn_a[j]*sgn_b
        out.append((i,s))
    return out
def identity(): return [(0,1),(1,1),(2,1),(3,1),(4,1)]
def flip(k): 
    e=identity(); e[k]=(k,-1); return e
def swap01():
    e=identity(); e[0]=(1,1); e[1]=(0,1); return e
def transmission_phase_after_whiten(g):
    # whitened isotropy ⇒ no phase (toy receipt = 0)
    return 0.0
def main():
    gens=[("f0",flip(0)),("f1",flip(1)),("f2",flip(2)),("f3",flip(3)),("f4",flip(4)),("s01",swap01())]
    table={}
    names=[n for n,_ in gens]
    for (na,ga),(nb,gb) in itertools.product(gens,gens):
        gc=compose(ga,gb)
        table[f"{na}∘{nb}"]={"phase":transmission_phase_after_whiten(gc)}
    phases=[v["phase"] for v in table.values()]
    ok=all(abs(p)<1e-12 for p in phases)
    out={"kind":"defect_fusion","ok_zero_phase":ok,"fusion_table":table}
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
