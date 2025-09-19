import io, json, sys
motive_path = sys.argv[1]
manifest_path = ".tau_ledger/manifest.json"
m = json.load(io.open(motive_path, "r", encoding="utf-8"))
try:
    man = json.load(io.open(manifest_path, "r", encoding="utf-8"))
except Exception:
    man = {"automorphic": []}
man.setdefault("automorphic", []).append(m)
io.open(manifest_path, "w", encoding="utf-8").write(json.dumps(man, ensure_ascii=False, indent=2))
print(f"[automorphic] motive {m.get("seed")} published")
