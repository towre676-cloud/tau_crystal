import os, json, time, hashlib
def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()
def now_id(prefix):
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    return f"{prefix}_{ts}", ts
def ensure_dirs():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
def write(prefix, payload):
    ensure_dirs()
    rid, ts = now_id(prefix)
    out = f"analysis/freed/{rid}.json"
    with open(out,"w",encoding="utf-8") as f: json.dump(payload, f, indent=2)
    mp = f".tau_ledger/freed/{rid}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f:
        json.dump({"run_id":rid,"timestamp_utc":ts,"artifacts":[{"path":out,"sha256":sha256_file(out)}]}, f, indent=2)
    print("[manifest]", mp)
def main():
    levels = os.environ.get("FREED_TMF_LEVELS","12,18,30")
    levels = [s.strip() for s in levels.split(",") if s.strip()]
    write("a5_tmf_stability",{
        "_inputs":{"levels":levels},
        "_claims":{"tmf_stability":"stub present; detailed TMF deltas WIP"},
        "_certificates":{"pass": False, "levels_count": len(levels)}
    })
if __name__=="__main__":
    main()
