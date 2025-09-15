import sys,io
p,f,t=sys.argv[1],sys.argv[2],sys.argv[3]
s=io.open(p,"r",encoding="utf-8").read()
io.open(p,"w",encoding="utf-8").write(s.replace(f,t))
