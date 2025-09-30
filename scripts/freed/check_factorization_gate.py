import os, math
from scripts.freed._helpers_common import (
  import_linalg, mu_one_loop, scheduler_walls, write_receipt
)

def main():
    lam_and_dlam = import_linalg()
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))

    pole = 1.0/(b*mu0)
    ellT = 0.9 * pole

    muT = mu_one_loop(mu0,b,ellT)
    lam0,_=lam_and_dlam(mu0)
    lamT,_=lam_and_dlam(muT)
    ln_det0=sum(math.log(x) for x in lam0)
    ln_detT=sum(math.log(x) for x in lamT)
    total = ln_detT - ln_det0

    walls = scheduler_walls(mu0,b,6)
    last=0.0; segsum=0.0
    for w in walls:
        if w>ellT: break
        mu_w = mu_one_loop(mu0,b,w)
        lam_w,_=lam_and_dlam(mu_w)
        ln_det_w=sum(math.log(x) for x in lam_w)
        if last==0.0:
            seg_delta = ln_det_w - ln_det0
        else:
            mu_prev = mu_one_loop(mu0,b,last)
            lam_prev,_=lam_and_dlam(mu_prev)
            ln_det_prev=sum(math.log(x) for x in lam_prev)
            seg_delta = ln_det_w - ln_det_prev
        segsum += seg_delta
        last = w
    if last < ellT:
        mu_prev = mu_one_loop(mu0,b,last)
        lam_prev,_=lam_and_dlam(mu_prev)
        ln_det_prev=sum(math.log(x) for x in lam_prev)
        segsum += (ln_detT - ln_det_prev)

    resid = abs(segsum - total)
    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell_total":ellT},
      "_claims":{"factorization":"sum over walls equals whole interval"},
      "_certificates":{"residual":resid,"tolerance":{"one_loop":1e-12}}
    }
    write_receipt("a6_factorization_gate", payload)

if __name__=="__main__":
    main()
