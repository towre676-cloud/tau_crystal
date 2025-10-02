cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
a="${1:-}"; b="${2:-}"; label="${3:-}"
[ -n "$a" ] && [ -n "$b" ] || { echo "[err] usage: braid_merge.sh <receiptA.json> <receiptB.json> [label]"; exit 2; }
[ -f "$a" ] || { echo "[err] missing: $a"; exit 3; }
[ -f "$b" ] || { echo "[err] missing: $b"; exit 4; }
sa=$(openssl dgst -sha256 "$a" | awk "{print \$2}")
sb=$(openssl dgst -sha256 "$b" | awk "{print \$2}")
ba=$(wc -c <"$a" | tr -d "[:space:]")
bb=$(wc -c <"$b" | tr -d "[:space:]")
ord1="$a"; ord2="$b"; s1="$sa"; s2="$sb"; b1="$ba"; b2="$bb"
if [ "$sa" ">" "$sb" ]; then ord1="$b"; ord2="$a"; s1="$sb"; s2="$sa"; b1="$bb"; b2="$ba"; fi
tmpc=".tmp.braid_concat.$$"; : > "$tmpc"; printf "%s%s" "$s1" "$s2" > "$tmpc"
braid_sha=$(openssl dgst -sha256 "$tmpc" | awk "{print \$2}")
rm -f "$tmpc"
hexxor() { h1="$1"; h2="$2"; perl -e '($a,$b)=@ARGV; $a=pack("H*",$a); $b=pack("H*",$b); $c=$a^$b; print unpack("H*",$c);' "$h1" "$h2"; }
xor_hex=$(hexxor "$sa" "$sb")
tmpx=".tmp.braid_xor.$$"; : > "$tmpx"; printf "%s" "$xor_hex" | xxd -r -p > "$tmpx" 2>/dev/null || true
xor_sha=$(openssl dgst -sha256 "$tmpx" | awk "{print \$2}")
rm -f "$tmpx"
ts="$(date -u +%FT%TZ)"
out=".tau_ledger/seifert/${ts//:/-}_braid.json"; : > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"label\":\"$(printf "%s" "$label" | sed 's/\"/\047/g')\"," >> "$out"
printf "%s" "\"ordering\":\"sha256_asc\",\"sources\":[" >> "$out"
printf "%s" "{\"path\":\"$(printf "%s" "$ord1" | sed 's/\"/\047/g')\",\"bytes\":$b1,\"sha256\":\"$s1\"}," >> "$out"
printf "%s" "{\"path\":\"$(printf "%s" "$ord2" | sed 's/\"/\047/g')\",\"bytes\":$b2,\"sha256\":\"$s2\"}]," >> "$out"
printf "%s" "\"braid\":{\"braid_sha256\":\"$braid_sha\",\"xor_sha256\":\"$xor_sha\"}}" >> "$out"
echo "[ok] braid → $out"
