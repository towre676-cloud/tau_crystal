from __future__ import annotations
import json, hashlib, time
from typing import Any, Dict, Optional

def canonical_json(obj: Dict[str,Any]) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

def manifest_sha256(canon: str) -> str:
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()

def serialize_manifest(run_id: str, matrix_digest_hex: str,
                       tau_series: Dict[str,Any], rank_report: Dict[str,Any],
                       qcro_trace: Optional[list] = None,
                       params: Optional[Dict[str,Any]] = None) -> Dict[str,Any]:
    payload = {
        "run_id": run_id,
        "timestamp": int(time.time()),
        "matrix_digest": matrix_digest_hex,
        "tau": {
            "alpha": tau_series.get("alpha"),
            "beta":  tau_series.get("beta"),
            "lmin":  tau_series.get("lmin"),
            "lmax":  tau_series.get("lmax"),
            "v0_norm": tau_series.get("v0_norm"),
            "E": tau_series.get("E"),
            "tau": tau_series.get("tau"),
        },
        "rank": rank_report,
        "qCRO": qcro_trace or [],
        "params": params or {},
    }
    canon = canonical_json(payload)
    payload["manifest_sha256"] = manifest_sha256(canon)
    return payload
