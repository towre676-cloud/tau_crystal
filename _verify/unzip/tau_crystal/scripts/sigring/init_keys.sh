#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
[ -f .tau_ledger/ed25519_priv.pem ] || openssl genpkey -algorithm ED25519 -out .tau_ledger/ed25519_priv.pem >/dev/null 2>&1
[ -f .tau_ledger/ed25519_pub.pem ]  || openssl pkey -in .tau_ledger/ed25519_priv.pem -pubout -out .tau_ledger/ed25519_pub.pem >/dev/null 2>&1
echo "[OK] keys ready: .tau_ledger/ed25519_{priv,pub}.pem"
