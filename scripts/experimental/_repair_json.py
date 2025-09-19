import sys, json, pathlib
def first_object_text(s:str)->str:
    i=s.find("{")
    if i<0: return ""
    obj,_=json.JSONDecoder().raw_decode(s[i:])
    return json.dumps(obj, sort_keys=True, separators=(",",":")) + "\n"
def main(p):
    t=pathlib.Path(p).read_text(encoding="utf-8", errors="replace")
    txt=first_object_text(t)
    if not txt: raise SystemExit(f"[repair] no JSON object in {p}")
    pathlib.Path(p).write_text(txt, encoding="utf-8")
    print("[repair]", p, "bytes=", len(txt))
if __name__=="__main__":
    for p in sys.argv[1:]: main(p)
