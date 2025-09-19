#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -E -o pipefail; set +H; umask 022
PYBIN=""; for c in python python3 py; do if command -v "$c" >/dev/null 2>&1; then PYBIN="$c"; break; fi; done
[ -n "$PYBIN" ] || { echo "[rg] no python found"; exit 2; }
[ "$PYBIN" = "py" ] && PYTAG="-3" || PYTAG=""
[ -x scripts/rg/affine_leaf.py ] || { echo "[rg] missing scripts/rg/affine_leaf.py"; exit 2; }
mkdir -p .tau_ledger/rg .tau_ledger/chain
"$PYBIN" $PYTAG scripts/rg/affine_leaf.py --json --out ".tau_ledger/rg/affine_leaf.json"
sha() {
  f="$1"
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$f" | cut -d" " -f1; return; fi
  if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$f" | cut -d" " -f1; return; fi
  if command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 "$f" | awk '{print $2}'; return; fi
  "$PYBIN" $PYTAG -c "import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],'rb').read()).hexdigest())" "$f"
}
sha_rg=$(sha ".tau_ledger/rg/affine_leaf.json")
printf "%s\n" "$sha_rg" > ".tau_ledger/rg/affine_leaf.sha256"
"$PYBIN" $PYTAG scripts/rg/assert_ok.py
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
printf "%s %s %s\n" "$ts" ".tau_ledger/rg/affine_leaf.json" "$sha_rg" >> ".tau_ledger/chain/CHAIN"
echo "[rg] appended chain entry for affine_leaf.json @ $ts"
