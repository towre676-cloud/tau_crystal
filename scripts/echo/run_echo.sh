#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
python3 - "$@" <<PY
import json,sys,math
from pathlib import Path
p=Path("artifacts/echo/cone_homology.json")
q=Path("artifacts/echo/freq_hist.json")
betti=json.loads(p.read_text())["betti"]
freq=json.loads(q.read_text())["freq"]
graded=sum(betti)
out={"graded_scalar":graded,"betti":betti,"freq_keys":sorted(freq.keys())}
print(json.dumps(out, separators=(\",\",\":\")))
PY
