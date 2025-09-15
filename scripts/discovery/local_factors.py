import json, os
def _load_json(p):
  try: return json.load(open(p,encoding="utf-8"))
  except Exception: return {}
def load_params():
  data={}
  for p in [
      ".tau_ledger/langlands/combined_ap_satake_stable.json",
      ".tau_ledger/langlands/ap_stable.json",
      ".tau_ledger/langlands/satake_stable.json",
      ".tau_ledger/langlands/combined_ap_satake.json",
      ".tau_ledger/langlands/ap.json",
      ".tau_ledger/langlands/satake.json",
      ".tau_ledger/langlands/L_tau.json",
      ".tau_ledger/langlands/rank.json",
      ".tau_ledger/experimental/fft_bsd.json",
  ]:

      ".tau_ledger/langlands/rank.json",
      ".tau_ledger/experimental/fft_bsd.json",
      ".tau_ledger/langlands/ap.json",
      ".tau_ledger/langlands/satake.json",
  ]:
    if os.path.isfile(p): data.update(_load_json(p))
  ap=data.get("ap") or data.get("hecke_ap") or {}
  sat=data.get("satake") or {}
  # Normalize keys
  ap={int(k):float(v) for k,v in ap.items()} if isinstance(ap,dict) else {}
  sat={int(k):tuple(v) for k,v in sat.items()} if isinstance(sat,dict) else {}
  N=int(data.get("level", data.get("N", 1)) or 1)
  k=int(data.get("weight", data.get("k", 0)) or 0)
  eps=data.get("epsilon", data.get("sign", 1))
  eps=1 if eps in (None, "", 0) else int(eps)
  Q=float(data.get("conductor", data.get("Q", N)))
  gamma=str(data.get("gamma_type","R"))
  return {"ap":ap, "satake":sat, "N":N, "k":k, "epsilon":eps, "Q":Q, "gamma":gamma}
def satake_from_ap(ap, p, k=0, chi=1):
  a=ap.get(p);
  if a is None: return None
  c=(p**(k-1))*chi
  disc=a*a - 4*c
  if disc>=0:
    r=disc**0.5; return ((a+r)/2.0, (a-r)/2.0)
  else:
    r=complex(0.0, (-disc)**0.5); return ((a+r)/2.0, (a-r)/2.0)
