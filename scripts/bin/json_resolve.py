#!/usr/bin/env python3
import sys, json, pathlib
from copy import deepcopy
def merge(a,b):
    if isinstance(a,dict) and isinstance(b,dict):
        out=dict(a); out.update(b); return out
    return deepcopy(b)
def resolve(o,root):
    if isinstance(o,dict):
        o={k:resolve(v,root) for k,v in o.items()}
        if "$include" in o and isinstance(o["$include"],str):
            inc=(root/o["$include"]).resolve()
            with inc.open("rb") as f: inc_obj=json.load(f)
            inc_obj=resolve(inc_obj,inc.parent)
            base={k:v for k,v in o.items() if k!="$include"}
            return merge(inc_obj,base)
        return o
    if isinstance(o,list):
        return [resolve(v,root) for v in o]
    return o
p=pathlib.Path(sys.argv[1]).resolve()
with p.open("rb") as f: obj=json.load(f)
robj=resolve(obj,p.parent)
s=json.dumps(robj,ensure_ascii=False,separators=(",",":"),sort_keys=True).encode("utf-8")
sys.stdout.buffer.write(s)
