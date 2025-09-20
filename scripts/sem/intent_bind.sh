#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
intent="$1"; target="${2:-}"
thash="-" ; [ -n "$target" ] && thash=$( ( [ -f "$target" ] && cat "$target" ) | (sha256sum 2>/dev/null || shasum -a 256 2>/dev/null || openssl dgst -sha256 -r) | awk "{print \$1}")
rid=$(scripts/crypto/sha256_stamp.sh "INTENT|$intent|$thash")
echo "$rid"
