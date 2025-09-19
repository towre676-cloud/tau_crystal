import sys, os, json, tempfile, pathlib
def first_object(s:str):
    i=s.find("{")
    if i<0: return None
    out=[]; depth=0; in_str=False; esc=False; started=False
    for ch in s[i:]:
        out.append(ch)
        if in_str:
            if esc: esc=False
            elif ch=="\\\\": esc=True
            elif ch=="\"": in_str=False
        else:
            if ch=="{": depth+=1; started=True
            elif ch=="}": depth-=1
            elif ch=="\"": in_str=True
            if started and depth==0: break
    txt="".join(out)
    try: obj=json.loads(txt)
    except Exception: return None
    return obj
def sanitize(path:str):
    p=pathlib.Path(path)
    s=p.read_text(encoding="utf-8", errors="replace")
    obj=first_object(s)
    if obj is None: raise SystemExit(f"[sanitize] no complete object in {path}")
    txt=json.dumps(obj, sort_keys=True, separators=(",",":")) + "\\n"
    tmp=path+".tmp"; pathlib.Path(tmp).write_text(txt, encoding="utf-8")
    os.replace(tmp, path); print("[sanitize]", path, "bytes=", len(txt))
if __name__=="__main__":
    for a in sys.argv[1:]: sanitize(a)
