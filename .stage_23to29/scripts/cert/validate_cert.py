#!/usr/bin/env python3
import sys, json, hashlib, os, zipfile, tempfile
from pathlib import Path

def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()

def load_manifest(cert_path: Path):
    if cert_path.is_file() and cert_path.suffix.lower()=='.zip':
        tmp = Path(tempfile.mkdtemp(prefix="cert_"))
        with zipfile.ZipFile(cert_path, 'r') as z: z.extractall(tmp)
        mans = list(tmp.rglob('MANIFEST.json'))
        if not mans: sys.exit("MANIFEST.json not found in zip")
        return json.loads(mans[0].read_text(encoding='utf-8')), tmp
    man = cert_path / "MANIFEST.json"
    if not man.exists(): sys.exit("MANIFEST.json not found in directory")
    return json.loads(man.read_text(encoding='utf-8')), cert_path

def main():
    if len(sys.argv) < 2:
        print("usage: validate_cert.py <cert_dir_or_zip>"); sys.exit(2)
    manifest, root = load_manifest(Path(sys.argv[1]).resolve())
    files = manifest.get("files", {})
    rows, ok_all, cat = [], True, []
    for rel, meta in sorted(files.items()):
        p = (root / rel)
        exists = p.exists()
        got = sha256(p) if exists else "(missing)"
        want = meta.get("sha256","")
        size_w = meta.get("bytes",-1)
        size_g = p.stat().st_size if exists else 0
        match = exists and got == want and size_g == size_w
        ok_all &= match
        if exists: cat.append(want)
        rows.append((rel, "OK" if match else "FAIL", want, got, size_w, size_g))
    root_want = manifest.get("root_sha256","")
    root_got = hashlib.sha256("".join(sorted(cat)).encode('utf-8')).hexdigest()
    root_ok = (root_want == root_got); ok_all &= root_ok

    w = max(12, max((len(r[0]) for r in rows), default=12))
    print(f"{'file':{w}}  status  sha256 (want)                           sha256 (got)                             bytes(want/got)")
    print("-"*w + "  ------  ----------------------------------------  ----------------------------------------  --------------")
    for rel, st, want, got, bw, bg in rows:
        print(f"{rel:{w}}  {st:6}  {want:>40}  {got:>40}  {bw}/{bg}")
    print("\nroot digest:", "OK" if root_ok else "FAIL", root_want, "==", root_got)
    sys.exit(0 if ok_all else 1)

if __name__ == "__main__":
    main()
