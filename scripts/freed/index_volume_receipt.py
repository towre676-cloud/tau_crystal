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
    ell  = 0.8 * pole
    mu   = mu_one_loop(mu0,b,ell)

    lam0,_ = lam_and_dlam(mu0)
    lamT,_ = lam_and_dlam(mu)
    ln_det0 = sum(math.log(x) for x in lam0)
    ln_detT = sum(math.log(x) for x in lamT)
    dln = ln_detT - ln_det0

    lnZ_ratio = -0.5 * dln
    Z_ratio = math.exp(lnZ_ratio)

    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell":ell,"log_base":base},
      "_claims":{"relative_index_gaussian":"logB ≈ -1/2 Δ log det Σ"},
      "_certificates":{"logB_gaussian": ln_to_base(lnZ_ratio, base), "volume_ratio": Z_ratio}
    }
    write_receipt("a10_index_volume", payload)

if __name__=="__main__":
    main()
