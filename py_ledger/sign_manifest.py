import json, base64, hashlib, sys, pathlib
def sign(path: str, sk_b64: str) -> str:
    p = pathlib.Path(path)
    data = json.loads(p.read_text())
    canon = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    h = hashlib.sha256(canon.encode("utf-8")).digest()
    scheme = "sha256-stub"; sig = h
    try:
        from nacl.signing import SigningKey
        sk = SigningKey(base64.b64decode(sk_b64))
        sig = sk.sign(h).signature
        scheme = "ed25519"
    except Exception:
        pass
    data["signature"] = {"scheme": scheme, "value": base64.b64encode(sig).decode("ascii")}
    p.write_text(json.dumps(data, indent=2))
    return scheme

if __name__ == "__main__":
    print(sign(sys.argv[1], sys.argv[2]))
