#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
src="${1:-}"; out="${2:-.tau_ledger/morpho/v_frontal.local}"
[ -f "$src" ] || { echo "usage: mesh_evenodd_stub.sh MESH.(obj|ply) [OUT.local]" >&2; exit 2; }
mkdir -p "$(dirname "$out")"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
case "$src" in
  *.obj|*.OBJ) awk 'tolower($1)=="v"{print $2,$3}' "$src" > "$tmp" ;;
  *.ply|*.PLY) awk 'BEGIN{hdr=1} /^end_header/{hdr=0;next} hdr{next} {if($1~/^[-+0-9.]/&&$2~/^[-+0-9.]/) print $1,$2}' "$src" > "$tmp" ;;
  *) echo "unsupported mesh extension"; exit 3;;
esac
rows=$(wc -l < "$tmp" | awk '{print $1}'); [ "$rows" -ge 3 ] || { echo "mesh too small"; exit 4; }
even=0; odd=0
while read -r x y; do
  ay=$(awk -v y="$y" 'BEGIN{print y}')      # even part magnitude ~ y
  dx=$(awk -v x="$x" 'BEGIN{print x}')      # odd part magnitude ~ x
  even=$(awk -v e="$even" -v a="$ay" 'BEGIN{print e + a*a}')
  odd=$(awk -v o="$odd" -v d="$dx" 'BEGIN{print o + d*d}')
done < "$tmp"
tot=$(awk -v e="$even" -v o="$odd" 'BEGIN{print e+o}')
H=$(awk -v e="$even" -v t="$tot" 'BEGIN{if(t==0) print "0"; else printf "%.8f", e/t}')
sha=$(sha256sum "$src" | awk '{print $1}'); ts=$(date -u +%Y%m%dT%H%M%SZ)
: > "$out"
printf "MOD=%s\nSRC=%s\nSHA256=%s\nEVEN=%s\nODD=%s\nH=%s\nTIME=%s\n" "v_frontal" "$src" "$sha" "$even" "$odd" "$H" "$ts" >> "$out"
echo "ok: mesh-evenodd -> $out (H=$H; n=$rows)"
