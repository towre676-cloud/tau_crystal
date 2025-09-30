import os, math
from scripts.freed._helpers_common import (
  import_linalg, mu_one_loop, log_base, ln_to_base, write_receipt
)

def weyl_cardinality(stack:str, phi_on:bool)->int:
    stack=stack.upper()
    if stack=="B5": return 3840
    if stack=="E6": return 51840
    return 3840

def main():
    lam_and_dlam = import_linalg()
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))
    base= os.environ.get("FREED_LOG_BASE","e").strip().lower()
    stack = os.environ.get("FREED_W_STACK","B5").strip()
    phi_on= os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}

    pole = 1.0/(b*mu0)
    ell  = 0.8 * pole
    mu   = mu_one_loop(mu0,b,ell)

    lam0,_ = lam_and_dlam(mu0)
    lamT,_ = lam_and_dlam(mu)
    ln_det0 = sum(math.log(x) for x in lam0)
    ln_detT = sum(math.log(x) for x in lamT)
    bulk_ln = ln_detT - ln_det0
    bulk = ln_to_base(bulk_ln, base)

    W = weyl_cardinality("E6" if phi_on else stack, phi_on)
    eta_half = 0.5 * log_base(W, base)
    index_Z = 0.0
    logB_total = bulk - eta_half + index_Z

    payload = {
      "_inputs":{"mu0":mu0,"b":b,"ell":ell,"stack":stack,"phi_twist":phi_on,"log_base":base},
      "_claims":{"APS_split":"logB = bulk - (eta/2) + IndZ"},
      "_certificates":{"bulk":bulk,"eta_half":eta_half,"indexZ":index_Z,"logB_total":logB_total}
    }
    write_receipt("a4_aps_split", payload)

if __name__=="__main__":
    main()
