#!/usr/bin/env python3
import sys, os, math
import numpy as np

def load_obj_xy(path):
    V=[]
    with open(path,'r',encoding='utf-8',errors='ignore') as f:
        for line in f:
            if line.startswith('v '):
                _,x,y,*rest=line.strip().split()
                V.append([float(x), float(y)])
    return np.array(V,float)

def save_obj_xy(path, V):
    with open(path,'w') as f:
        for x,y in V:
            f.write(f"v {x:.6f} {y:.6f} 0.0\n")

def voxel_downsample(V, cell=0.005):
    # grid by rounding to voxel centers
    G = np.floor(V/cell).astype(np.int64)
    # unique voxel keys
    from collections import defaultdict
    buckets=defaultdict(list)
    for i,g in enumerate(map(tuple,G)):
        buckets[g].append(i)
    out=[]
    for idxs in buckets.values():
        out.append(V[idxs[0]])  # pick first (could do mean)
    return np.array(out,float)

def main():
    if len(sys.argv)<4:
        print("usage: mesh_downsample.py IN.obj OUT.obj voxel_size", file=sys.stderr); sys.exit(2)
    IN, OUT, s = sys.argv[1], sys.argv[2], float(sys.argv[3])
    V = load_obj_xy(IN)
    if V.shape[0]==0: raise SystemExit("no vertices")
    Vs = voxel_downsample(V, cell=max(1e-6, s))
    save_obj_xy(OUT, Vs)
    print(f"downsampled: {V.shape[0]} -> {Vs.shape[0]}")
if __name__=="__main__":
    main()
