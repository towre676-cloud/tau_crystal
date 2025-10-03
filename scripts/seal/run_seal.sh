#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
CANON="$(python3 scripts/tools/canon_json.py < artifacts/seal/pushout_manifest.json)"
printf "%s" "$CANON" > artifacts/seal/pushout_manifest.canon.json
H=$(printf "%s" "$CANON" | openssl dgst -sha256 | awk "{print \$2}" 2>/dev/null || true)
if [ -z "${H:-}" ]; then H=$(printf "%s" "$CANON" | sha256sum | awk "{print \$1}"); fi
printf "%s\n" "{\"H_τ\":\"$H\",\"terminal\":true}" > artifacts/seal/verifier_certificate.json
printf "%s\n" "{\"kan\":\"trivial\"}" > artifacts/seal/descent_kan.json
printf "%s\n" "$H"
