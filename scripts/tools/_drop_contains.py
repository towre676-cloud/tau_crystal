import sys,io
p,sub=sys.argv[1],sys.argv[2]
s=io.open(p,"r",encoding="utf-8").read().splitlines()
io.open(p,"w",encoding="utf-8").write("\n".join([l for l in s if sub not in l])+"\n")
