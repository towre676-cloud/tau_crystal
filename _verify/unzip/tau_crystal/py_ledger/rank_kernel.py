from __future__ import annotations
import numpy as np, hashlib
from typing import Dict, Any, List

DEFAULT_PRIMES = [1999993, 1999997, 1999999]

def _modinv(a: int, p: int) -> int:
    return pow(a % p, p-2, p)

def modular_rank_with_trace(M: np.ndarray, primes: List[int] = None) -> Dict[str, Any]:
    if primes is None: primes = DEFAULT_PRIMES
    if M.dtype.kind not in ("i","u"):
        M = np.rint(M).astype(np.int64, copy=False)
    m, n = M.shape
    ranks: Dict[int,int] = {}
    pivot_digest = hashlib.sha256()
    transcripts: List[str] = []
    for p in primes:
        A = (M % p).astype(np.int64, copy=True)
        r = 0; transcript=[]
        for c in range(n):
            piv = None
            for i in range(r, m):
                if A[i,c] % p != 0: piv = i; break
            if piv is None: continue
            if piv != r:
                A[[r,piv],:] = A[[piv,r],:]; transcript.append(f"p={p} swap r={r} i={piv}")
            pv = int(A[r,c] % p); inv = _modinv(pv, p)
            A[r,:] = (A[r,:] * inv) % p
            transcript.append(f"p={p} pivot c={c} r={r} pv={pv}")
            for i in range(m):
                if i == r: continue
                f = int(A[i,c] % p)
                if f != 0:
                    A[i,:] = (A[i,:] - f * A[r,:]) % p
            r += 1
            if r == m: break
        ranks[p] = r
        t = (";".join(transcript)).encode("utf-8")
        transcripts.append(t.decode("utf-8"))
        pivot_digest.update(hashlib.sha256(t).digest())
    return {"rank_over_primes":ranks,
            "rank_over_Q_estimate": int(max(ranks.values()) if ranks else 0),
            "pivot_digest_hex": pivot_digest.hexdigest(),
            "transcripts": transcripts}
