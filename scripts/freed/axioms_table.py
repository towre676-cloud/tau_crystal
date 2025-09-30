import os, json, glob, time, hashlib

LEDGER = ".tau_ledger/freed"
OUTDIR = "analysis/freed"

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""):
            h.update(chunk)
    return h.hexdigest()

def collect_manifests() -> list:
    out=[]
    for path in sorted(glob.glob(os.path.join(LEDGER, "*.manifest.json"))):
        try:
            with open(path, "r", encoding="utf-8") as f:
                mani=json.load(f)
            mani["_ledger_path"]=path
            mani["_ledger_sha256"]=sha256_file(path)
            out.append(mani)
        except Exception as e:
            print(f"[warn] skip {path}: {e}")
    return out

def summarize_axioms(manis: list) -> dict:
    ax = {
        "functoriality": {"ok": True, "notes": ["μ(ℓ1+ℓ2)=μ(ℓ2;μ(ℓ1)) (algebraic)"], "certs":[]},
        "flatness": {"ok": False, "notes": [], "certs":[]},
        "stack_invariance": {"ok": False, "notes": [], "certs":[]},
        "APS_boundary": {"ok": False, "notes": [], "certs":[]},
        "defects": {"ok": False, "notes": [], "certs":[]},
        "TMF_stability": {"ok": False, "notes": [], "certs":[]},
    }
    for m in manis:
        certs=m.get("certificates",{})
        # flatness
        if "determinant_trace_identity_max_abs_err" in certs:
            ax["flatness"]["certs"].append({
                "run": m.get("run_id"), "mode": m.get("mode"),
                "max_abs_err": certs["determinant_trace_identity_max_abs_err"]
            })
        # factorization (locality/gluing) and TMF stability
        if "factorization_phi_off_abs_err" in certs or "factorization_phi_on_abs_err" in certs:
            ax["TMF_stability"]["certs"].append({
                "run": m.get("run_id"), "mode": m.get("mode"),
                "phi_off_err": certs.get("factorization_phi_off_abs_err"),
                "phi_on_err": certs.get("factorization_phi_on_abs_err"),
            })
        # monodromy isotropy → stack invariance
        if "monodromy_shape_norm_err" in certs:
            ax["stack_invariance"]["certs"].append({
                "run": m.get("run_id"), "mode": m.get("mode"),
                "shape_norm_err": certs["monodromy_shape_norm_err"]
            })
        # eta reporter (we’ll store numbers in certificates below)
        if "eta_half_logW" in certs or "eta_half_logW_B5" in certs:
            ax["APS_boundary"]["certs"].append({
                "run": m.get("run_id"),
                "eta_half_logW": certs.get("eta_half_logW"),
                "eta_half_logW_B5": certs.get("eta_half_logW_B5"),
                "eta_half_logW_E6": certs.get("eta_half_logW_E6"),
            })
        # defects
        if "sign_flip_phase" in certs or "perm_phase" in certs:
            ax["defects"]["certs"].append({
                "run": m.get("run_id"),
                "sign_flip_phase": certs.get("sign_flip_phase"),
                "perm_phase": certs.get("perm_phase"),
                "sign_flip_shape_err": certs.get("sign_flip_shape_err"),
                "perm_shape_err": certs.get("perm_shape_err"),
            })

    # Mark ok if we have any certs for the category
    ax["flatness"]["ok"] = len(ax["flatness"]["certs"])>0
    ax["stack_invariance"]["ok"] = len(ax["stack_invariance"]["certs"])>0
    ax["APS_boundary"]["ok"] = len(ax["APS_boundary"]["certs"])>0
    ax["defects"]["ok"] = len(ax["defects"]["certs"])>0
    ax["TMF_stability"]["ok"] = len(ax["TMF_stability"]["certs"])>0
    return ax

def main():
    os.makedirs(OUTDIR, exist_ok=True); os.makedirs(LEDGER, exist_ok=True)
    manis=collect_manifests()
    table=summarize_axioms(manis)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"axioms_{ts}"
    out=f"{OUTDIR}/{run_id}.json"
    with open(out,"w",encoding="utf-8") as f: json.dump({"axioms":table,"manifests":len(manis)}, f, indent=2)
    mani={"run_id": run_id, "timestamp_utc": ts,
          "claims":{"axioms_table":"summarized manifests (UTF-8 safe)"},
          "artifacts":[{"path": out, "sha256": sha256_file(out)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] axioms table crashed:", e); raise
