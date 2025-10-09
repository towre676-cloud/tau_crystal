import sys, json
def get(d, path):
    cur = d
    for k in path.split("."):
        if isinstance(cur, dict) and k in cur:
            cur = cur[k]
        else:
            print("") ; sys.exit(0)
    if isinstance(cur, (dict, list)):
        import json ; print(json.dumps(cur, separators=(",",":")))
    else:
        print(str(cur))
if __name__ == "__main__":
    p,f = sys.argv[1], sys.argv[2]
    with open(f,"r",encoding="utf-8") as fh:
        d = json.load(fh)
    get(d,p)
