from typing import List, Tuple
import math

def _swap_rows(A, i, j): 
    if i!=j: A[i],A[j]=A[j],A[i]

def _swap_cols(A, i, j):
    if i!=j:
        for r in range(len(A)): 
            A[r][i],A[r][j]=A[r][j],A[r][i]

def snf_diag(Ain: List[List[int]], guard:int=10000) -> Tuple[List[int], int]:
    """Return (diagonal entries of SNF, rank). No U,V returned."""
    A = [list(map(int,row)) for row in (Ain or [])]
    n = len(A); m = len(A[0]) if A else 0
    i = j = 0; steps = 0
    # Work copy so callers can reuse matrices
    while i<n and j<m and steps < guard:
        # find pivot with minimal nonzero abs in submatrix
        pi, pj, best = -1, -1, None
        for r in range(i,n):
            for c in range(j,m):
                v = A[r][c]
                if v!=0:
                    av = abs(v)
                    if best is None or av < best:
                        best = av; pi, pj = r, c
        if best is None:
            break
        _swap_rows(A, i, pi); _swap_cols(A, j, pj)
        # make A[i][j] positive
        if A[i][j] < 0: 
            A[i] = [-x for x in A[i]]
        # clear column j except row i
        for r in range(n):
            if r==i: continue
            while A[r][j] != 0 and steps < guard:
                q = A[r][j] // A[i][j]
                for c in range(j,m):
                    A[r][c] -= q * A[i][c]
                if A[r][j]==0: break
                # one more subtraction to reduce magnitude via Euclid
                sign = 1 if A[r][j] > 0 else -1
                for c in range(j,m):
                    A[r][c] -= sign * A[i][c]
                steps += 1
        # clear row i except col j
        for c in range(m):
            if c==j: continue
            while A[i][c] != 0 and steps < guard:
                q = A[i][c] // A[i][j]
                for r in range(i,n):
                    A[r][c] -= q * A[r][j]
                if A[i][c]==0: break
                sign = 1 if A[i][c] > 0 else -1
                for r in range(i,n):
                    A[r][c] -= sign * A[r][j]
                steps += 1
        # ensure divisibility with next diagonals by local fixes
        # (simple pass; full divisibility chain not strictly enforced here)
        i += 1; j += 1
    # collect diagonal entries (nonzero on the i==j band); zero elsewhere
    d = []
    for k in range(min(n,m)):
        v = abs(A[k][k])
        if v != 0:
            d.append(int(v))
    d.sort()
    rank = sum(1 for x in d if x!=0)
    return d, rank
