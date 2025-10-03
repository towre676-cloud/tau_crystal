import sys,hashlib,os
def h(p):
    m=hashlib.sha256()
    with open(p,"rb") as f:
        for chunk in iter(lambda: f.read(65536), b""): m.update(chunk)
    return m.hexdigest()
for p in sys.argv[1:]:
    if os.path.isfile(p) and os.path.getsize(p)>0:
        print(h(p), p)
    else:
        print("MISSING", p)
