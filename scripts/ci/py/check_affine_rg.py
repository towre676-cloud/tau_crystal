import json, glob, hashlib
def load_two():
    C = sorted(glob.glob("analysis/affine_rg/*_canon.json"))[-2:]
    assert len(C) >= 2, "need two canon payloads"
    return [json.load(open(p, "r", encoding="utf-8")) for p in C]
def norm(D):
    s = float(D.get("reparam_scalar", 1))
    b   = float(D["b"])   / s
    mu0 = float(D["mu0"]) / s
    ell = float(D["ell"]) / s
    two_loop = bool(D.get("two_loop", False))
    omega    = str(D.get("omega", ""))
    return {"b": b, "mu0": mu0, "ell": ell, "two_loop": two_loop, "omega": omega}
def close(a, b, eps=1e-12): return abs(a - b) <= eps
A, B = load_two(); NA, NB = norm(A), norm(B)
assert close(NA["b"],   NB["b"])
assert close(NA["mu0"], NB["mu0"])
assert close(NA["ell"], NB["ell"])
assert NA["two_loop"] == NB["two_loop"] and NA["omega"] == NB["omega"]
canon = lambda X: json.dumps(X, sort_keys=True, separators=(",", ":")).encode("utf-8")
ha = hashlib.sha256(canon(NA)).hexdigest()
hb = hashlib.sha256(canon(NB)).hexdigest()
assert ha == hb, f"normalized digest differed: {ha} != {hb}"
print("[ok] affine_rg: scalar-reparam invariant check passed; normalized digests equal")
