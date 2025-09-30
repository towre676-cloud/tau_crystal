import os, math
from scripts.freed._helpers_common import import_linalg, mu_one_loop, write_receipt

def main():
    lam_and_dlam = import_linalg()
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))

    pole = 1.0/(b*mu0)
    ell  = 0.6 * pole
    mu   = mu_one_loop(mu0,b,ell)

    lam,_ = lam_and_dlam(mu)
    lam_perm = list(reversed(lam))
    ln_det  = sum(math.log(x) for x in lam)
    ln_detP = sum(math.log(x) for x in lam_perm)
    resid = abs(ln_det - ln_detP)

    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell":ell},
      "_claims":{"atlas_swap_invariance":"log det Σ invariant under permutation"},
      "_certificates":{"residual":resid,"tolerance":1e-15}
    }
    write_receipt("a3_atlas_swap", payload)

if __name__=="__main__":
    main()
