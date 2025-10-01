#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
python3 scripts/receipt/bind_receipt.py analysis/modular/mod_canon.json
python3 - <<PY
import json,math,sys
d=json.load(open("analysis/modular/mod_canon.json","r",encoding="utf-8"))
def row_to_complex_pair(row):
    # row like [Re11,Im11, Re12,Im12]
    return complex(row[0],row[1]), complex(row[2],row[3])
S1,S2 = row_to_complex_pair(d["S"][0]), row_to_complex_pair(d["S"][1])
S = [[S1[0],S1[1]],[S2[0],S2[1]]]
T = [[complex(d["T"][0][0],d["T"][0][1]),0j],[0j,complex(d["T"][1][0],d["T"][1][1])]]
def mm(A,B):
    n=len(A); C=[[0j]*n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            s=0j
            for j in range(n): s+=A[i][j]*B[j][k]
            C[i][k]=s
    return C
def dag(A): n=len(A); return [[A[j][i].conjugate() for j in range(n)] for i in range(n)]
def close(A,B,eps=1e-9):
    n=len(A)
    for i in range(n):
        for j in range(n):
            if abs(A[i][j]-B[i][j])>eps: return False
    return True
I=[[1+0j,0j],[0j,1+0j]]
assert close(mm(S,dag(S)), I, 1e-8), "S not unitary"
# T diagonal phases: here T=I is fine; also check det S ~= 1/sqrt(2)^2 - 1/sqrt(2)^2 = -1? Not needed; keep minimal.
print("[modular] S unitary OK")
PY
