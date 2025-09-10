import json
from typing import Any, Dict, List

def align_qcro_with_tau(qcro_path: str, tau_series: Dict[str, Any]) -> List[Dict[str, Any]]:
    tau = (tau_series or {}).get("tau", []) or []
    kmax = max(0, len(tau)-1)
    out = []
    with open(qcro_path, "r", encoding="utf-8") as fh:
        for i, line in enumerate(fh):
            line = line.strip()
            if not line: continue
            rec = json.loads(line)
            rec["tau"] = (tau[min(i, kmax)] if kmax>0 else 0.0)
            out.append(rec)
    return out
