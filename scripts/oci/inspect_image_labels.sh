cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
img="${1:-}"; [ -n "$img" ] || { echo "[err] usage: inspect_image_labels.sh <image:tag>"; exit 2; }
ts="$(date -u +%FT%TZ)"; out=".tau_ledger/oci/${ts//:/-}_inspect.json"; : > "$out"
j="$(docker image inspect "$img" | tr -d "\r")" || { echo "[err] docker inspect failed"; exit 3; }
sha=$(printf "%s" "$j" | sed -n 's/.*"org.tau_crystal.receipt_sha256":"\([^"]*\)".*/\1/p')
: > "$out"; printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"image\":\"$(printf "%s" "$img" | sed 's/"/'/g')\",\"receipt_sha256\":\"$sha\"" >> "$out"
printf %s "}" >> "$out"; echo "[ok] wrote → $out"
