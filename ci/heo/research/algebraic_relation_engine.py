#!/usr/bin/env python3
# minimal skeleton — more will be appended in next chunks
import json, argparse, glob

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--glob", default="ci/data/sequences/*.json")
    args = ap.parse_args()
    seqs = sorted(glob.glob(args.glob))
    print(json.dumps({"status":"ok","sequences_seen":len(seqs)}, indent=2))

if __name__ == "__main__":
    main()
