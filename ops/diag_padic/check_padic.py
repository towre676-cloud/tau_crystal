import json, sys
with open('analysis/padic/p_canon.json','r',encoding='utf-8') as f:
    d = json.load(f)

a = d['h']['num'] % d['p']
b = d['h']['den'] % d['p']
p = d['p']

inv = None
for x in range(1, p):
    if (b * x) % p == 1:
        inv = x
        break

res = (a * (inv if inv is not None else 0)) % p
print("[vals]", "a=", a, "b=", b, "p=", p, "inv=", inv, "res=", res)
sys.exit(0 if inv is not None else 1)
