import os, math
from scripts.freed._helpers_common import (
  import_linalg, mu_one_loop, dmu_dell_one_loop, write_receipt
)

def main():
    lam_and_dlam = import_linalg()
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))

    pole = 1.0/(b*mu0)
    ell  = 0.8 * pole
    K = 24
    max_abs_err = 0.0

    for j in range(K):
        t = ell * (j/(K-1))
        mu = mu_one_loop(mu0,b,t)
        lam, dlam_dmu = lam_and_dlam(mu)
        dmu = dmu_dell_one_loop(mu,b)
        tr_series = sum((dlam_dmu[i]*dmu)/lam[i] for i in range(5))

        h = max(1e-8*ell, 1e-12)
        mu_f = mu_one_loop(mu0,b,t+h)
        lam_f,_ = lam_and_dlam(mu_f)
        ln_det = sum(math.log(x) for x in lam)
        ln_det_f = sum(math.log(x) for x in lam_f)
        fd = (ln_det_f - ln_det)/h
        max_abs_err = max(max_abs_err, abs(tr_series - fd))

    mu_mid = mu_one_loop(mu0,b,0.5*ell)
    lam_m,_ = lam_and_dlam(mu_mid)
    h = max(1e-6*ell, 1e-10)
    mu_p = mu_one_loop(mu0,b,0.5*ell + h)
    lam_p,_ = lam_and_dlam(mu_p)
    ln_det_m = sum(math.log(x) for x in lam_m)
    ln_det_p = sum(math.log(x) for x in lam_p)
    hol = (ln_det_p - ln_det_m)/h + (ln_det_m - ln_det_p)/h

    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell":ell},
      "_claims":{"trace_identity":"tr(Σ^{-1}∂ℓΣ) = ∂ℓ log det Σ","holonomy_zero":"flat away from pole"},
      "_certificates":{"max_abs_err":max_abs_err,"holonomy_estimate":abs(hol),
                       "tolerances":{"trace":1e-10,"holonomy":1e-12}}
    }
    write_receipt("a2_curvature", payload)

if __name__=="__main__":
    main()
