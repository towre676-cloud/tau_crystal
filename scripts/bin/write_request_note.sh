#!/usr/bin/env bash
set -Eeuo pipefail
set +H
umask 022

usage(){ echo "usage: write_request_note.sh <stem> [outdir=receipts]" >&2; exit 2; }

stem="${1:-}"; outdir="${2:-receipts}"
[ -n "$stem" ] || usage
mkdir -p "$outdir"

# locate digest (prefer outdir, then .tau_ledger)
digest_file=""
if [ -f "$outdir/$stem.sha256" ]; then
  digest_file="$outdir/$stem.sha256"
elif [ -f ".tau_ledger/$stem.sha256" ]; then
  digest_file=".tau_ledger/$stem.sha256"
else
  echo "[err] missing digest: $outdir/$stem.sha256 (and .tau_ledger fallback not found)" >&2
  exit 3
fi

# locate preimage path (prefer outdir, then .tau_ledger, else infer canonical default)
preimage_path_file=""
if [ -f "$outdir/$stem.preimage.path" ]; then
  preimage_path_file="$outdir/$stem.preimage.path"
elif [ -f ".tau_ledger/$stem.preimage.path" ]; then
  preimage_path_file=".tau_ledger/$stem.preimage.path"
elif [ -f "analysis/${stem}.request.canon.json" ]; then
  printf "%s\n" "analysis/${stem}.request.canon.json" > "$outdir/$stem.preimage.path"
  preimage_path_file="$outdir/$stem.preimage.path"
else
  echo "[err] cannot resolve preimage path for stem '$stem'" >&2
  exit 4
fi

# read values (trim whitespace on digest)
d="$(tr -d '\r\n' < "$digest_file")"
p="$(cat "$preimage_path_file")"

# write note JSON with minimal escaping
note="$outdir/$stem.request.note.json"
: > "$note"
printf "%s" '{"request_sha256":"' >> "$note"
printf "%s" "$d" >> "$note"
printf "%s" '","preimage_path":"' >> "$note"
printf "%s" "$p" | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' >> "$note"
printf "%s\n" "\"}" >> "$note"

# mirror for legacy tools, if present
[ -d ".tau_ledger" ] && cp -f -- "$note" ".tau_ledger/$stem.request.note.json" || :

# print the note path
printf "%s\n" "$note"
exit 0
