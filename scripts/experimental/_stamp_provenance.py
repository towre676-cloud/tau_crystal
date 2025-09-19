import os, json, pathlib, platform, hashlib, datetime, tempfile
def _run_id()->str:
    rid=os.environ.get("GITHUB_RUN_ID")
    if rid: return rid
    now=datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
    return "local:"+now.isoformat().replace("+00:00","Z")
def _merkle(path: str)->str:
    try:
        data=pathlib.Path(path).read_bytes()
    except Exception:
        return "0"*64
    return hashlib.sha256(data).hexdigest()
def _first_obj(path: str):
    s=pathlib.Path(path).read_text(encoding="utf-8",errors="replace")
    i=s.find("{")
    if i<0: return {}
    obj,_=json.JSONDecoder().raw_decode(s[i:])
    return obj
def stamp(path:str):
    obj=_first_obj(path)
    prov=obj.get("provenance",{})
    now=datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00","Z")
    prov.update({
        "run_id": _run_id(),
        "timestamp": now,
        "machine": platform.node(),
        "merkle_root": _merkle(path),
    })
    obj["provenance"]=prov
    txt=json.dumps(obj, sort_keys=True, separators=(",",":")) + "\n"
    tmp=path+".tmp"
    pathlib.Path(tmp).write_text(txt, encoding="utf-8")
    os.replace(tmp, path)
if __name__=="__main__":
    import sys
    for p in sys.argv[1:]: stamp(p)
