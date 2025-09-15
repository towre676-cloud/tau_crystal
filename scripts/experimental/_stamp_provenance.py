import io,json,os,sys,datetime,hashlib,subprocess
def run(cmd): return subprocess.check_output(cmd,shell=True,encoding='utf-8').strip()
target=sys.argv[1]
obj=json.load(io.open(target,"r",encoding="utf-8"))
commit=run("git rev-parse HEAD")
run_id=os.environ.get("GITHUB_RUN_ID","local")
machine=run("uname -n")
timestamp=datetime.datetime.utcnow().isoformat()+"Z"
tau_print=run("sha256sum .tau_ledger/seq/tau.csv 2>/dev/null | cut -d' ' -f1") or "0"*64
merkle_root=run("cat .tau_ledger/MERKLE_ROOT 2>/dev/null") or "0"*64
obj["provenance"]={
  "commit":commit,"run_id":run_id,"timestamp":timestamp,
  "machine":machine,"tau_print":tau_print,"merkle_root":merkle_root
}
io.open(target,"w",encoding="utf-8").write(json.dumps(obj,ensure_ascii=False,indent=2)+"\n")
print("stamped",target)
