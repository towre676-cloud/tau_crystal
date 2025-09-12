#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
sigdir=".tau_ledger/signals"; outdir=".tau_ledger/tau"; mkdir -p "$outdir"
mapfile -t files < <(ls "$sigdir"/signal-*.tsv 2>/dev/null || true)
[ "${#files[@]}" -gt 0 ] || { echo "[err] no signals in $sigdir/signal-*.tsv" >&2; exit 2; }
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
awk -v FS="[\t ]+" -v OFS="\t" 'FNR==NR{t[$1]=1; next} END{}' /dev/null 2>/dev/null || true
join_cmd(){ :
}
cp "${files[0]}" "$tmp";
for f in "${files[@]:1}"; do
  join -a 1 -a 2 -e NA -o auto "$tmp" "$f" > "${tmp}.j" || { echo "[err] join failed on $f" >&2; exit 3; }
  mv "${tmp}.j" "$tmp"
done
awk -v FS="[ \t]+" -v OFS="\t" '{ for(i=1;i<=NF;i++){ if($i=="") $i="NA"} ; print }' "$tmp" > "${tmp}.norm"
mv "${tmp}.norm" "$tmp"
awk -v FS="[ \t]+" -v OFS="\t" '{ print > "/dev/fd/3"; for(i=2;i<=NF;i++) if($i=="") $i="NA"; }' 3>"${tmp}.raw" "$tmp" >/dev/null 2>&1 || true
awk -v FS="[ \t]+" -v OFS="\t" '{print}' "$tmp" | awk -f scripts/bin/pav.awk > "$outdir/ensemble.tsv"
echo "$outdir/ensemble.tsv"
