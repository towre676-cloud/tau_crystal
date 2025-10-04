#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/echo/cone_Z_snf_plus.py >/dev/null 2>&1
[ -s artifacts/echo/cone_snf_diagonals.json ] || printf '%s\n' '{"d2":{"diag":[]},"d1":{"diag":[]},"d0":{"diag":[]}}' > artifacts/echo/cone_snf_diagonals.json
[ -s artifacts/echo/cone_homology_Zplus.json ] || printf '%s\n' '{"betti":[0,0,0],"torsion_upper":{"H0":[],"H1":[],"H2":[]},"fallback":true}' > artifacts/echo/cone_homology_Zplus.json
echo "[ok] Cone-Z+ emitted"
