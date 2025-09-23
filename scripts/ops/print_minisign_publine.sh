#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
PUB="${1:-$HOME/.keys/minisign.pub}"
test -f "$PUB" || { echo "missing $PUB" >&2; exit 1; }
echo -n "Seller public key (minisign): "; cat "$PUB" | tr -d "\r\n" ; echo
