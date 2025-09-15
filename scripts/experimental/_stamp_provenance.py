import io, json, os, sys, hashlib, datetime, platform, subprocess, re
def git_sha():
  try: return subprocess.check_output(["git","rev-parse","HEAD"],encoding="utf-8").strip()
  except Exception: return "0"*40
def sha256_file(p):
  try:
    h=hashlib.sha256();
    with open(p,"rb") as f:
      for chunk in iter(lambda: f.read(65536), b""): h.update(chunk)
    return h.hexdigest()
  except Exception: return "0"*64
def read_text(p):
  try: return io.open(p,"r",encoding="utf-8").read().strip()
  except Exception: return "0"*64
target=sys.argv[1]
txt=io.open(target,"r",encoding="utf-8").read()
# auto-repair: replace trailing literal "\\n" after a closing brace with a real newline; keep first balanced JSON only
txt=re.sub(r"}\\\\n\\s*$", "}\\n", txt)
depth=0; end=None; in_str=False; esc=False
for i,ch in enumerate(txt):
  if in_str:
    if esc: esc=False
    elif ch=="\\\\": esc=True
    elif ch=="\\"": in_str=False
  else:
    if ch=="\\"": in_str=True
    elif ch in "{[": depth+=1
    elif ch in "}]" and depth>0: depth-=1
    if depth==0 and end is None: end=i+1
txt = txt[:end] if end else txt
obj=json.loads(txt)
if not isinstance(obj,dict) or "data" not in obj:
  obj={"data": obj}
prov={
  "commit": git_sha(),
  "run_id": os.environ.get("GITHUB_RUN_ID","local"),
  "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
  "machine": platform.node() or "unknown",
  "tau_print": sha256_file(".tau_ledger/seq/tau.csv"),
  "merkle_root": read_text(".tau_ledger/MERKLE_ROOT")
}
obj["provenance"]=prov
io.open(target,"w",encoding="utf-8").write(json.dumps(obj,ensure_ascii=False,indent=2)+"\n")
print("stamped", target)
