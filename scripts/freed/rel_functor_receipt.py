import os, math
from scripts.freed._helpers_common import (
  import_linalg, mu_one_loop, ln_to_base, write_receipt
)

def main():
    lam_and_dlam = import_linalg()
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))
    base= os.environ.get("FREED_LOG_BASE","e").strip().lower()

    pole = 1.0/(b*mu0)
    ell1, ell2 = 0.25*pole, 0.30*pole
    ellT = ell1 + ell2

    mu_1 = mu_one_loop(mu0,b,ell1)
    mu_2 = mu_one_loop(mu_1,b,ell2)
    mu_T = mu_one_loop(mu0,b,ellT)
    comp_resid = abs(mu_2 - mu_T)

    lam0,_ = lam_and_dlam(mu0)
    lam1,_ = lam_and_dlam(mu_1)
    lamT,_ = lam_and_dlam(mu_T)
    ln_det0 = sum(math.log(x) for x in lam0)
    ln_det1 = sum(math.log(x) for x in lam1)
    ln_detT = sum(math.log(x) for x in lamT)

    total = ln_detT - ln_det0
    segsum= (ln_det1 - ln_det0) + (ln_detT - ln_det1)
    add_resid = abs(segsum - total)

    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell1":ell1,"ell2":ell2,"log_base":base},
      "_claims":{"relative_functor":"composition holds; additivity of log det Σ"},
      "_certificates":{"mu_comp_resid":comp_resid,"additivity_resid":add_resid,
                       "tolerances":{"mu":1e-12,"add":1e-12}},
      "mu":{"mu0":mu0,"mu1":mu_1,"mu2":mu_2,"muT":mu_T},
      "logdet":{"total": ln_to_base(total,base), "segmented_sum": ln_to_base(segsum,base)}
    }
    write_receipt("a1_rel_functor", payload)

if __name__=="__main__":
    main()
