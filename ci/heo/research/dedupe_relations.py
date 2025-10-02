#!/usr/bin/env python3
"""
Deduplicate discovered relation receipts by canonical signature,
and write a compact index 'receipts/heo/discovered/unique_index.json'.
"""
import json, glob, os, sys, hashlib

def signature_of(receipt):
    meta = receipt.get("metadata", {})
    t = meta.get("type")
    seq = meta.get("seq_basename", "")
    if t == "equality_in_k":
        return f"{seq}|eqk|d={meta.get('d')}|k={meta.get('k')}|kp={meta.get('k_prime')}"
    if t == "periodicity":
        return f"{seq}|per|d={meta.get('d')}|p={meta.get('period')}"
    if t == "cross_degree_equality":
        return f"{seq}|xdeg|d1={meta.get('d1')}|k1={meta.get('k1')}|d2={meta.get('d2')}|k2={meta.get('k2')}"
    # fallback: hash all metadata
    return f"{seq}|other|" + hashlib.sha256(json.dumps(meta, sort_keys=True).encode()).hexdigest()

def main():
    out_dir = "receipts/heo/discovered"
    files = sorted(glob.glob(os.path.join(out_dir, "*.json")))
    uniques = {}
    bucket = {}
    for f in files:
        try:
            obj = json.load(open(f))
        except Exception:
            continue
        sig = signature_of(obj)
        bucket.setdefault(sig, []).append({
            "id": obj.get("id"),
            "path": f,
            "type": obj.get("metadata", {}).get("type"),
            "seq": obj.get("metadata", {}).get("seq_basename")
        })
        if sig not in uniques:
            uniques[sig] = bucket[sig][0]

    index = {
        "unique_count": len(uniques),
        "unique": list(uniques.values()),
        "groups": bucket
    }
    json.dump(index, open(os.path.join(out_dir, "unique_index.json"), "w"), indent=2)
    print(json.dumps({"unique": len(uniques), "total": len(files)}, indent=2))

if __name__ == "__main__":
    main()
