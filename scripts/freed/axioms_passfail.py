import os, json, glob, time, hashlib

def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()

def latest(pattern):
    files = sorted(glob.glob(pattern))
    return files[-1] if files else None

def load_json(p):
    if not p: return {}
    try:
        with open(p,"r",encoding="utf-8") as f: return json.load(f)
    except Exception:
        return {}

def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out=f"analysis/freed/axioms_passfail_{ts}.json"

    a1 = load_json(latest("analysis/freed/a1_rel_functor_*.json"))
    a2 = load_json(latest("analysis/freed/a2_curvature_*.json"))
    a3 = load_json(latest("analysis/freed/a3_atlas_swap_*.json"))
    a4 = load_json(latest("analysis/freed/a4_aps_split_*.json"))
    a5 = load_json(latest("analysis/freed/a5_tmf_stability_*.json"))
    a6 = load_json(latest("analysis/freed/a6_factorization_gate_*.json"))
    a7 = load_json(latest("analysis/freed/a7_defect_fusion_*.json"))
    a9 = load_json(latest("analysis/freed/a9_branch_loop_*.json"))
    a10= load_json(latest("analysis/freed/a10_index_volume_*.json"))

    pf_fun  = load_json(latest("analysis/freed/axiom_functoriality_*.json"))
    pf_flat = load_json(latest("analysis/freed/axiom_flatness_*.json"))
    pf_stack= load_json(latest("analysis/freed/axiom_stack_equivariance_*.json"))
    pf_aps  = load_json(latest("analysis/freed/axiom_aps_accounting_*.json"))

    res = {
      "relative_functor":   (a1.get("_certificates",{}).get("mu_comp_resid",1.0) < 1e-10
                             and a1.get("_certificates",{}).get("additivity_resid",1.0) < 1e-10),
      "curvature_trace":    (a2.get("_certificates",{}).get("max_abs_err",1.0) < 1e-9),
      "holonomy_flat":      (a2.get("_certificates",{}).get("holonomy_estimate",1.0) < 1e-12),
      "atlas_swap":         (a3.get("_certificates",{}).get("residual",1.0) < 1e-12),
      "factorization_gate": (a6.get("_certificates",{}).get("residual",1.0) < 1e-10),
      "defect_fusion":      bool(a7.get("_certificates",{}).get("fusion_ok",False)),
      "aps_present":        ("bulk" in a4.get("_certificates",{}) and "eta_half" in a4.get("_certificates",{})),
      "relative_index":     ("logB_gaussian" in a10.get("_certificates",{})),
      "tmf_stability":      bool(a5.get("_certificates",{}).get("pass",False)),
      "branch_loop_invariance": (a9.get("_certificates",{}).get("worst_rel_change",1.0) < 1e-9),
      "functoriality_two_loop": (pf_fun.get("_certificates",{}).get("mu_comp_two_loop",1.0) < 1e-9),
      "flatness_strong":    (pf_flat.get("_certificates",{}).get("max_trace_abs_err",1.0) < 1e-10),
      "stack_equivariance": (pf_stack.get("_certificates",{}).get("residual",1.0) < 1e-12),
      "aps_accounting":     (pf_aps.get("_certificates",{}).get("abs_gap",1.0) < 1e-9)
    }

    payload = {"passfail":res, "timestamp_utc": ts}
    with open(out,"w",encoding="utf-8") as f: json.dump(payload, f, indent=2)

    mp=f".tau_ledger/freed/axioms_passfail_{ts}.manifest.json"
    mani={"run_id":f"axioms_passfail_{ts}","timestamp_utc":ts,
          "artifacts":[{"path":out,"sha256":sha256_file(out)}],
          "claims":{"axioms_passfail":"PASS/FAIL summary from latest receipts"}}
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    main()
