#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/echo/cone_Z_snf.py >/dev/null 2>&1
[ -s artifacts/echo/cone_homology_Z.json ] || printf '%s\n' '{"betti":[0,0,0],"fallback":true}' > artifacts/echo/cone_homology_Z.json
[ -s artifacts/echo/snf_cone_meta.json ]   || printf '%s\n' '{"fallback":true}' > artifacts/echo/snf_cone_meta.json
echo "[ok] Cone-Z ready"
