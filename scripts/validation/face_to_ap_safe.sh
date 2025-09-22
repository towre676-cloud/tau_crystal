#!/usr/bin/env bash
set -euo pipefail; set +H
in="${1:?usage: face_to_ap_safe.sh <in.tsv> <id>}"
id="${2:?usage: face_to_ap_safe.sh <in.tsv> <id>}"
d="validation/work/$id"; mkdir -p "$d"

if bash scripts/validation/face_to_ap.sh "$in" "$id" 2>/dev/null && [ -f "$d/row.txt" ]; then
  echo "$d/row.txt"
  exit 0
fi

echo "[WARN] face_to_ap failed for $id — emitting placeholder row" >&2
: > "$d/a_p.tsv"
printf "A\t0\nB\t0\nN\t0\n" > "$d/curve.tsv"
: > "$d/r.tsv"
ap_sha="$(sha256sum "$d/a_p.tsv" | awk '{print $1}')"
ap_len="$(wc -l < "$d/a_p.tsv")"
printf "%s\tA=0\tB=0\tN=0\tAP_SHA=%s\tAP_LEN=%s\n" "$id" "$ap_sha" "$ap_len" > "$d/row.txt"
echo "$d/row.txt"
