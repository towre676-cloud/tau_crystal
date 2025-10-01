#!/usr/bin/env python3
import json, hashlib, os, random
random.seed(13)
def canon_hash(vec):
    s=",".join(f"{x:+.6f}" for x in sorted(vec,key=lambda z:-abs(z)))
    return hashlib.sha256(s.encode()).hexdigest()
def permute(v,p): return [v[i] for i in p]
def main():
    v=[0.33,-0.5,0.1666667,0.0, -0.3333333]
    h0=canon_hash(v)
    perms=[(1,0,2,3,4),(2,1,0,3,4),(4,3,2,1,0)]
    matches=[]
    for p in perms:
        h=canon_hash(permute(v,p))
        matches.append(h==h0)
    out={"kind":"atlas_swap","base":h0,"matches":matches,"pass":all(matches)}
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
