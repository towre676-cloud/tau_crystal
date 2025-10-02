cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
img="${1:-}"; [ -n "$img" ] || { echo "[err] usage: verify_docker_receipt_label.sh <image:tag>"; exit 2; }
manifest_json="$(docker image inspect "$img" | tr -d "\r")"
printf "%s\n" "$manifest_json" | grep -q 'org.tau_crystal.receipt_sha256' || { echo "[err] missing receipt label"; exit 3; }
sha=$(printf "%s\n" "$manifest_json" | tr -d "\n" | sed "s/.*org.tau_crystal.receipt_sha256\":\"\\([a-f0-9]*\\)\".*/\\1/")
[ -n "$sha" ] || { echo "[err] empty receipt label"; exit 4; }
echo "[ok] receipt label: $sha"
