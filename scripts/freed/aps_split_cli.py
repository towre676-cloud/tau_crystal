#!/usr/bin/env python3
import json, math, os
def mu(b, mu0, ell): return mu0/(1.0 - b*mu0*ell)
def bulk_integrand(b, mu0, ell):
    # toy integrand proportional to μ(ell); replace with your scored integrand
    return b*mu(b, mu0, ell)
def integrate_bulk(b, mu0, L, n=2048):
    s=0.0; h=L/n
    for k in range(n):
        a=k*h; m=a+h/2
        s+= bulk_integrand(b, mu0, m)
    return s*h
def eta_weyl(phi_active=False):
    # toy η capturing 3840 orbit reduction and φ tilt; tweak as needed
    base = math.log(3840.0)
    return base + (0.0 if not phi_active else 0.05)
def main():
    b=float(os.getenv("APS_B","1.0")); mu0=float(os.getenv("APS_MU0","0.1")); L=float(os.getenv("APS_ELL","0.5"))
    phi_on = bool(int(os.getenv("APS_PHI","0")))
    bulk = integrate_bulk(b, mu0, L)
    # define modeled logB and compare to APS split
    logB_model = bulk - 0.5*eta_weyl(phi_on)
    out = {
      "kind":"aps_split",
      "params":{"b":b,"mu0":mu0,"ell":L,"phi_on":phi_on},
      "bulk_integral":bulk,
      "eta_term":eta_weyl(phi_on),
      "reconstructed_logB":logB_model
    }
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
