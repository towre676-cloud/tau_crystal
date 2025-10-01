#!/usr/bin/env python3
import os, json, re, csv, hashlib, time
from pathlib import Path
def canon_sha256(d):
    b=json.dumps(d,sort_keys=True,separators=(\",\",\":\")).encode()
    return hashlib.sha256(b).hexdigest()
def last_conf_from_logs(p):
    for d in [p.parent,p.parent.parent]:
        if not d or not d.exists(): continue
        best=None; mt=-1.0
        for q in d.iterdir():
            n=q.name.lower()
            if q.suffix.lower() not in [".log",".txt"] or "face" not in n: continue
            try: s=q.read_text(encoding="utf-8",errors="ignore")
            except: continue
            m=re.findall(r"confidence\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)",s,re.I)
            if not m: continue
            try: t=q.stat().st_mtime
            except: t=time.time()
            if t>mt: mt=t; best=float(m[-1])
        if best is not None: return best
    return None
def tier(c):
    if c is None: return "unknown"
    return "0.99–1.00" if c>=0.99 else ("0.97–0.99" if c>=0.97 else ("0.95–0.97" if c>=0.95 else "<0.95"))
def find_metrics(p):
    conv=sym=None
    for d in [p.parent,p.parent.parent]:
        if not d or not d.exists(): continue
        for q in d.iterdir():
            n=q.name.lower(); sfx=q.suffix.lower()
            if sfx==".json" and ("metric" in n or "fusion" in n or "face" in n):
                try:
                    j=json.load(open(q,"r",encoding="utf-8"))
                    for k,v in j.items():
                        lk=k.lower()
                        if conv is None and "convexity" in lk:
                            try: conv=float(v)
                            except: pass
                        if sym is None and "rms" in lk and ("symmetry" in lk or "bilateral" in lk):
                            try: sym=float(v)
                            except: pass
                except: pass
            if sfx in [".log",".txt"] and "face" in n:
                try:
                    for line in open(q,"r",encoding="utf-8",errors="ignore"):
                        if conv is None:
                            m=re.search(r"convexity\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)",line,re.I)
                            if m: conv=float(m.group(1))
                        if sym is None:
                            m=re.search(r"(symmetry|bilateral).*?rms\\s*=\\s*([0-9]+(?:\\.[0-9]+)?)",line,re.I)
                            if m: sym=float(m.group(m.lastindex))
                except: pass
    return conv, sym
def main():
    root=Path(".").resolve(); out=root/".tau_ledger"/"census"; out.mkdir(parents=True,exist_ok=True)
    seen={}
    for dp,_,fns in os.walk(root):
        base=os.path.basename(dp)
        if base in {".git",".lake","node_modules"}: continue
        if "face_trace.json" not in fns: continue
        p=Path(dp)/"face_trace.json"
        try: d=json.loads(p.read_text(encoding="utf-8"))
        except: continue
        sig=d.get("face_signature"); h=sig if isinstance(sig,str) and len(sig)>=16 else canon_sha256(d)
        c=d.get("face_confidence")
        try: c=float(c)
        except: c=None
        if c is None: c=last_conf_from_logs(p)
        conv,sym=find_metrics(p)
        mt=0.0
        try: mt=p.stat().st_mtime
        except: pass
        row={"hash":h,"convexity_deg":conv,"symmetry_rms":sym,"confidence":c,"tier":tier(c),"path":str(p.relative_to(root))}
        score=(c if c is not None else -1.0, mt, 0 if (conv is not None or sym is not None) else 1)
        if h not in seen or score>seen[h][0]: seen[h]=(score,row)
    rows=[v[1] for v in seen.values()]
    rows.sort(key=lambda r:( {"0.99–1.00":0,"0.97–0.99":1,"0.95–0.97":2,"unknown":3,"<0.95":4}.get(r["tier"],9), -(r["confidence"] or -1)))
    with (out/"census.tsv").open("w",encoding="utf-8",newline="") as f:
        w=csv.writer(f,delimiter="\\t"); w.writerow(["hash","convexity_deg","symmetry_rms","confidence","tier","source_path"])
        for r in rows: w.writerow([r["hash"],r["convexity_deg"],r["symmetry_rms"],r["confidence"],r["tier"],r["path"]])
    cnt={}; [cnt.__setitem__(r["tier"],cnt.get(r["tier"],0)+1) for r in rows]
    with (out/"summary.tsv").open("w",encoding="utf-8",newline="") as f:
        w=csv.writer(f,delimiter="\\t"); w.writerow(["tier","count"])
        for k in ["0.99–1.00","0.97–0.99","0.95–0.97","unknown","<0.95"]:
            if k in cnt: w.writerow([k,cnt[k]])
    print(f"[census] rows={len(rows)}  out={out}")
    for r in rows[:5]: print(" -",r["hash"],r["confidence"],r["tier"],r["path"])
if __name__=="__main__": main()
