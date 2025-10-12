#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import sys, json, os, decimal
def jload(p):
  with open(p,"r",encoding="utf-8") as f: return json.load(f)
def dump(obj,p):
  class Enc(json.JSONEncoder):
    def default(self,o):
      if isinstance(o,decimal.Decimal): return format(o,"f")
      return json.JSONEncoder.default(self,o)
  s=json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(",",":"),cls=Enc)
  with open(p,"w",encoding="utf-8",newline="\\n") as f: f.write(s)
def argdict(argv):
  if len(argv)%2!=0:
    print("stack_pack.py: ERROR: arguments must be key-value pairs", file=sys.stderr); sys.exit(64)
  return {argv[i].lstrip("-"): argv[i+1] for i in range(0,len(argv),2)}
def main():
  argv = argdict(sys.argv[1:])
  for k in ("geo","alpha","raw","out"):
    if k not in argv: print(f"stack_pack.py: ERROR: missing --{k}", file=sys.stderr); sys.exit(64)
  geo=argv["geo"]; alpha=argv["alpha"]; rawd=argv["raw"]; outp=argv["out"]
  spec_hash=argv.get("spec-hash",""); env_hash=argv.get("env-hash",""); result_hash=argv.get("result-hash","")
  rawp=os.path.join(rawd,"fiber_raw.json")
  if not os.path.isfile(rawp): print(f"stack_pack.py: ERROR: missing {rawp}", file=sys.stderr); sys.exit(66)
  raw=jload(rawp)
  fiber={
    "alpha": str(alpha),
    "hashes":{"spec":spec_hash,"env":env_hash,"result":result_hash},
    "geometry":raw.get("geometry",{}),
    "grid":raw.get("grid",{"tau":["i","0.5i","0.7745966692i","1.154700538i"],"z":["0","1/6","1/3","1/2"]}),
    "multiplier":{"char":raw.get("mult_char","trivial"),"index":"3/2","label":"theta","level":raw.get("level",1)},
    "normalization":{"statement":"Ell(tau,0)=chi(X)","chi":raw.get("geometry",{}).get("chi"),"ell_tau0":raw.get("slices",{}).get("tau0")},
    "newton_girard":{"identity":"sum(x_i^3)=3c_3","factor":3},
    "sturm_cert":raw.get("sturm_cert",{}),
    "mde_cert":raw.get("mde_cert",{}),
    "rademacher":{"polars":raw.get("polars",[]),"termination":raw.get("polar_cert",{})},
    "window":{"nmax":raw.get("nmax",120),"rmax":raw.get("rmax",6)},
    "coeffs":raw.get("coeffs",{}),
    "numerics":{"residuals":raw.get("automorphy",{}),"mde_sup_resid":raw.get("mde",{}).get("sup_residual","0.0"),"policy":{"quantization":"fixed-decimal","places":16,"rounding":"round-half-even"}},
    "physics":raw.get("physics",{})
  }
  dump(fiber,outp)
if __name__=="__main__": main()
