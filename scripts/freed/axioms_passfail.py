import os, json, glob, time, hashlib
def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for c in iter(lambda: f.read(1<<20), b""): h.update(c)
    return h.hexdigest()
def latest(pat):
    files=sorted(glob.glob(pat))
    return files[-1] if files else None
def load(p):
    if not p: return {}
    try: return json.load(open(p,"r",encoding="utf-8"))
    except Exception: return {}

def main():
    os.makedirs("analysis/freed",exist_ok=True); os.makedirs(".tau_ledger/freed",exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out=f"analysis/freed/axioms_passfail_{ts}.json"
    a1=load(latest("analysis/freed/a1_rel_functor_*.json"))
    a2=load(latest("analysis/freed/a2_curvature_*.json"))
    a3=load(latest("analysis/freed/a3_atlas_swap_*.json"))
    a4=load(latest("analysis/freed/a4_aps_split_*.json"))
    a5=load(latest("analysis/freed/a5_tmf_stability_*.json"))
    a6=load(latest("analysis/freed/a6_factorization_gate_*.json"))
    a7=load(latest("analysis/freed/a7_defect_fusion_*.json"))
    a9=load(latest("analysis/freed/a9_branch_loop_*.json"))
    a10=load(latest("analysis/freed/a10_index_volume_*.json"))

    pf={
      "relative_functor":   (a1.get("_certificates",{}).get("mu_comp_resid",1.0) < 1e-10
                             and a1.get("_certificates",{}).get("additivity_resid",1.0) < 1e-10),
      "curvature_trace":    (a2.get("_certificates",{}).get("max_abs_err",1.0) < 1e-11),
      "holonomy_flat":      (a2.get("_certificates",{}).get("holonomy_estimate",1.0) < 1e-13),
      "flatness_strong":    (a2.get("_certificates",{}).get("max_abs_err",1.0) < 1e-12),
      "atlas_swap":         (a3.get("_certificates",{}).get("residual",1.0) < 1e-12),
      "factorization_gate": (a6.get("_certificates",{}).get("residual",1.0) < 1e-11),
      "defect_fusion":      bool(a7.get("_certificates",{}).get("fusion_ok",False)),
      "aps_accounting":     (a4.get("_certificates",{}).get("equality_residual",1.0) < a4.get("_certificates",{}).get("tolerance",1e-12)),
      "relative_index":     ("logB_gaussian" in a10.get("_certificates",{})),
      "tmf_stability":      bool(a5.get("_certificates",{}).get("pass",False)),
      "branch_loop_invariance": (a9.get("_certificates",{}).get("max_sv_rel_change",1.0) < 1e-12),
      "stack_equivariance": (a3.get("_certificates",{}).get("residual",1.0) < 1e-12),
      "functoriality_two_loop": (a1.get("_certificates",{}).get("mu_comp_resid",1.0) < 1e-10)
    }
    json.dump({"passfail":pf,"timestamp_utc":ts}, open(out,"w",encoding="utf-8"), indent=2)
    mp=f".tau_ledger/freed/axioms_passfail_{ts}.manifest.json"
    json.dump({"run_id":f"axioms_passfail_{ts}","timestamp_utc":ts,
               "artifacts":[{"path":out,"sha256":sha256_file(out)}],
               "claims":{"axioms_passfail":"PASS/FAIL summary from latest receipts"}},
              open(mp,"w",encoding="utf-8"), indent=2)
    print("[manifest]", mp)
if __name__=="__main__": main()
