import sys,io
p,sub,new=sys.argv[1],sys.argv[2],sys.argv[3]
s=io.open(p,"r",encoding="utf-8").read().splitlines()
for i,l in enumerate(s):
    if sub in l:
        s.insert(i+1,new)
        break
io.open(p,"w",encoding="utf-8").write("\n".join(s)+"\n")
