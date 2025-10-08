import json, hashlib
p = 'tsv/elliptic_pass2_receipt.json'
with open(p,'r') as f: d = json.load(f)
d['artifacts'] = dict(sorted(d.get('artifacts',{}).items()))
d2 = dict(d); d2.pop('merkle_root', None)
canon = json.dumps(d2, separators=(',',':'), ensure_ascii=False)
h = hashlib.sha256(canon.encode()).hexdigest()
d['merkle_root'] = h
with open(p,'w') as f: json.dump(d, f, indent=2, ensure_ascii=False)
