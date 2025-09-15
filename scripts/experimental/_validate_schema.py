import io,json,re,sys,glob
def ok_hex(s,n): return isinstance(s,str) and re.fullmatch(r"[0-9a-f]{"+str(n)+r"}", (s or "")) is not None
def validate_one(path):
  try:
    obj=json.load(io.open(path,"r",encoding="utf-8"))
  except Exception as e:
    print(f"[ERR] %s: JSON parse failed: %s" % (path, e)); return 1
  if not isinstance(obj,dict): print(f"[ERR] %s: not an object" % path); return 1
  if "provenance" not in obj or "data" not in obj:
    print(f"[ERR] %s: missing top-level keys {provenance,data}" % path); return 1
  p=obj["provenance"]; req=["commit","run_id","timestamp","machine","tau_print","merkle_root"]
  for k in req:
    if k not in p: print(f"[ERR] %s: provenance.%s missing" % (path,k)); return 1
  if not ok_hex(p["commit"],40):      print(f"[ERR] %s: bad commit" % path); return 1
  if not ok_hex(p["tau_print"],64):   print(f"[ERR] %s: bad tau_print" % path); return 1
  if not ok_hex(p["merkle_root"],64): print(f"[ERR] %s: bad merkle_root" % path); return 1
  print("✓", path); return 0
def main():
  paths = sys.argv[1:] or glob.glob(".tau_ledger/experimental/*.json")
  rc=0
  for f in paths: rc |= validate_one(f)
  sys.exit(rc)
if __name__=="__main__": main()
