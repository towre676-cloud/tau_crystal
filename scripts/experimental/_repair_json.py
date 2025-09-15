import io,sys,json
def repair(s):
  try: json.loads(s); return s
  except: pass
  depth=end=0; inq=esc=False
  for i,ch in enumerate(s):
    if inq:
      esc = (not esc and ch=="\\\\" )
      if not esc and ch=="\\"": inq=False
      continue
    if ch=="\\"": inq=True
    elif ch in "{[": depth+=1
    elif ch in "}]": depth=max(0,depth-1)
    if depth==0: end=i+1
  return s[:end] if end else s
for p in sys.argv[1:]:
  t=io.open(p,"r",encoding="utf-8").read(); io.open(p,"w",encoding="utf-8").write(repair(t))
  print("repaired",p)
