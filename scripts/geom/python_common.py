import hashlib, json, os, sys, numpy as np
def sha256_bytes(b: bytes)->str: return hashlib.sha256(b).hexdigest()
def sha256_path(p:str)->str:
    h=hashlib.sha256()
    with open(p,"rb") as f: [h.update(chunk) for chunk in iter(lambda:f.read(1<<20),b"")]
    return h.hexdigest()
def stable_json(obj)->str: return json.dumps(obj, sort_keys=True, separators=(",",":"))
def write_tsv_line(path, cols):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path,"a",encoding="utf-8") as f: f.write("\t".join(str(c) for c in cols)+"\n")
