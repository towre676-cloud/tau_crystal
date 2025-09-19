#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
ts=$(date -u +"%Y%m%dT%H%M%SZ")
out=".tau_ledger/attest/attest-${ts}.json"
: > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/attest/v1\"," >> "$out"
printf "%s\n" "  \"timestamp\":\"${ts}\"," >> "$out"
printf "%s\n" "  \"uname\":\"$(uname -a | sed 's/"/\\"/g')\"," >> "$out"
printf "%s\n" "  \"os_release\":\"$(cat /etc/os-release 2>/dev/null | tr -d \"\\r\" | tr \"\\n\" \"|\" | sed 's/"/\\"/g')\"," >> "$out"
printf "%s\n" "  \"bash\":\"$(bash --version | head -n1 | sed 's/"/\\"/g')\"," >> "$out"
printf "%s\n" "  \"sha_bin_sh\":\"$( [ -x /bin/sh ] && sha256sum /bin/sh 2>/dev/null | cut -d\" \" -f1 )\"," >> "$out"
printf "%s\n" "  \"tools\":{\"git\":\"$(git --version)\",\"jq\":\"$(command -v jq >/dev/null 2>&1 && jq --version || echo none)\"}" >> "$out"
printf "%s\n" "}" >> "$out"
echo "[attest] $out"
