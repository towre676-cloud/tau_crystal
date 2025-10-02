#!/usr/bin/env python3
import json, argparse, math

def load_sequence(path):
    with open(path,"r") as f:
        obj=json.load(f)
    patt=obj["pattern"]; T=len(patt)
    return patt, T

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--sequence", required=True)
    ap.add_argument("--beta", type=float, default=0.7)
    args=ap.parse_args()
    patt,T=load_sequence(args.sequence)
    H=sum(patt)/T
    P=math.log(1 - H + H*math.exp(args.beta))
    print(json.dumps({"H":H, "beta":args.beta, "P_formula":P}, indent=2))
    N=10000
    ones=sum(patt[i%T] for i in range(N))
    approx = ((N-ones) + math.exp(args.beta)*ones)/N
    print(json.dumps({"empirical_linear_combo": approx}, indent=2))

if __name__=="__main__":
    main()
