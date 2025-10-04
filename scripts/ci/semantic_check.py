#!/usr/bin/env python3
"""Semantic validator for tau_crystal certificates (ASCII-only)."""
import json, math, sys
from pathlib import Path

def wrap_2pi(x):
    # principal value in (-pi, pi]
    return (x + math.pi) % (2 * math.pi) - math.pi

def approx(a, b, tol):
    return abs(a - b) <= tol

def check_descent(cert, tol_obs=1e-6):
    r = cert["descent_certificate"]
    for U, v in r["restrictions"].items():
        if not approx(v["residue"], v["abs_residue"] - v["baseline_abs_residue"], tol_obs):
            return False, f"Residue mismatch in {U}"
    coco = r["cocycle"]["delta_phi_phase"]
    hol  = r["holonomy"]["int_trK_phase"]
    obs  = r["obs_mod_2pi"]
    if not approx(wrap_2pi(coco - hol), obs, tol_obs):
        return False, f"Obstruction mismatch: {obs} != wrap({coco} - {hol})"
    return True, "OK"

def check_reflection(cert, tol_res=1e-6, tol_det=1e-9):
    r = cert["reflection_certificate"]
    f, rv = r["forward"], r["reverse"]
    if not approx(f["residue"] + rv["residue"], 0.0, tol_res):
        return False, f"Residue not anti-symmetric: {f['residue']} + {rv['residue']}"
    if not approx(f["det_abs"], rv["det_abs"], tol_det):
        return False, f"Determinant mismatch: {f['det_abs']} != {rv['det_abs']}"
    gap = r["spectral_gap"]
    expected = "positive-definite" if gap["min"] >= gap["epsilon_gap"] else "hermitian-only"
    if r["positivity_claim"] != expected:
        return False, f"Positivity claim '{r['positivity_claim']}' inconsistent with gap {gap['min']}"
    return True, "OK"

def check_cone(cert):
    r = cert["cone_certificate"]
    if not r["witness_exact"]:
        return False, "witness_exact is false"
    if r["quillen_distance"] > r["epsilon_quillen"]:
        return False, f"Quillen distance {r['quillen_distance']} > {r['epsilon_quillen']}"
    if r["curvature_additivity_residual"] > r["epsilon_curv"]:
        return False, f"Curvature residual {r['curvature_additivity_residual']} > {r['epsilon_curv']}"
    if not r["distinguished"]:
        return False, "Distinguished flag is false despite predicates passing"
    return True, "OK"

def main():
    root = Path(__file__).parent.parent.parent
    examples = root / "certificates" / "examples"
    checks = {"descent": check_descent, "reflection": check_reflection, "cone": check_cone}
    passed = 0; failed = 0
    for cert_file in sorted(examples.glob("*.json")):
        ctype = next((k for k in checks if k in cert_file.stem), None)
        if not ctype:
            print(f"[skip] {cert_file.name} (unknown type)"); continue
        try:
            cert = json.loads(Path(cert_file).read_text(encoding="utf-8"))
            ok, msg = checks[ctype](cert)
            print(f"[✓] {cert_file.name}: {msg}" if ok else f"[✗] {cert_file.name}: {msg}")
            passed += 1 if ok else 0
            failed += 0 if ok else 1
        except Exception as e:
            print(f"[✗] {cert_file.name}: {e}"); failed += 1
    print(f"\n[summary] passed={passed} failed={failed}")
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
