import os, sys, time, json, glob, pathlib
def wait_quiet(p, quiet_ms=700, timeout_s=12):
    path=pathlib.Path(p);
    if not path.exists(): return False
    dl=time.time()+timeout_s
    last=(path.stat().st_mtime_ns, path.stat().st_size)
    while time.time()<dl:
        time.sleep(0.15)
        cur=(path.stat().st_mtime_ns, path.stat().st_size)
        if cur==last:
            time.sleep(quiet_ms/1000.0)
            if (path.stat().st_mtime_ns, path.stat().st_size)==cur: return True
        last=cur
    return True
def first_object(s:str):
    i=s.find("{");
    if i<0: return None
    out=[]; depth=0; instr=False; esc=False; started=False
    for ch in s[i:]:
        out.append(ch)
        if instr:
            if esc: esc=False
            elif ch=="\\\\": esc=True
            elif ch=="\"": instr=False
        else:
            if ch=="{": depth+=1; started=True
            elif ch=="}": depth-=1
            elif ch=="\"": instr=True
            if started and depth==0: break
    txt="".join(out)
    try: return json.loads(txt)
    except Exception: return None
def canon_atomic(p):
    wait_quiet(p)
    s=pathlib.Path(p).read_text(encoding="utf-8",errors="replace")
    obj=first_object(s)
    if obj is None: print("[guard-skip]",p,"no JSON"); return False
    txt=json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n"
    tmp=p+".tmp"; pathlib.Path(tmp).write_text(txt,encoding="utf-8"); os.replace(tmp,p)
    json.load(open(p,encoding="utf-8"))
    print("[guard-ok]",p,"bytes",len(txt)); return True
def main(args):
    files = args or glob.glob(".tau_ledger/automorphic/*.json")
    if not files: print("[guard] no automorphic JSON found"); return 0
    ok=True
    for p in files: ok = canon_atomic(p) and ok
    return 0 if ok else 1
if __name__=="__main__": sys.exit(main(sys.argv[1:]))
