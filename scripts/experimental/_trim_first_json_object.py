import sys,os,json
def trim(p):
  s=open(p,"r",encoding="utf-8",errors="replace").read()
  out=[]; depth=0; i=0; n=len(s); instr=False; esc=False; started=False
  while i<n:
    ch=s[i]
    if instr:
      out.append(ch)
      if esc: esc=False
      elif ch=="\\\\": esc=True
      elif ch=="\"": instr=False
    else:
      if ch=="{": depth+=1; started=True; out.append(ch)
      elif ch=="}": out.append(ch); depth-=1
      elif ch=="\"": instr=True; out.append(ch)
      elif started: out.append(ch)
      if started and depth==0: break
    i+=1
  txt="".join(out).strip()
  obj=json.loads(txt)
  open(p,"w",encoding="utf-8").write(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n")
  # verify
  json.load(open(p,encoding="utf-8"))
  print("[trimmed]",p,"bytes=",len(txt))
if __name__=="__main__":
  for p in sys.argv[1:]:
    if os.path.isfile(p): trim(p)
