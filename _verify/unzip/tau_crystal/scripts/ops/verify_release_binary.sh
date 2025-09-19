#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
BIN="tau_verify-x86_64-unknown-linux-musl"
URL="https://github.com/towre676-cloud/tau_crystal/releases/latest/download/${BIN}"
curl -fsSL -o "$BIN" "$URL"
curl -fsSL -o "${BIN}.sig" "${URL}.sig"
curl -fsSL -o "${BIN}.cert" "${URL}.cert"
chmod +x "$BIN"
if command -v cosign >/dev/null 2>&1; then
  cosign verify-blob --certificate "${BIN}.cert" --signature "${BIN}.sig" --certificate-identity-regexp ".*" --certificate-oidc-issuer-regexp ".*" "$BIN" >/dev/null
elif [ -f cosign.pub ]; then
  echo "[warn] cosign not installed; verifying signature with repo pubkey unsupported here"
fi
./"$BIN" . >/dev/null && echo "[ok] rust verifier passed" || { echo "[err] rust verifier failed"; exit 3; }
