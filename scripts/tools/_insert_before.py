import sys,io
p,marker,frag=sys.argv[1],sys.argv[2],sys.argv[3]
s=io.open(p,"r",encoding="utf-8").read().splitlines(True)
f=io.open(frag,"r",encoding="utf-8").read()
for i,l in enumerate(s):
    if marker in l:
        s.insert(i,f)
        break
io.open(p,"w",encoding="utf-8").write("".join(s))
