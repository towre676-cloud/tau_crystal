#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
root() { cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1; }
root

# inputs
C=e29_curve_data.txt
K=k3_invariants.txt
F=k3_fibration_structure.txt
P=e29_points_x_coords.txt
R=e29_root_number.txt
W=framework_predictions.txt

# helpers
val() { grep -E "^$1: " "$2" | head -1 | sed "s/^$1: //"; }
hashf() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; elif command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 "$1" | awk "{print \$2}"; else printf "nohash"; fi; }
iso() { date -u +"%Y-%m-%dT%H:%M:%SZ"; }

# harvest curve
a1=$(val "a1" "$C")
a2=$(val "a2" "$C")
a3=$(val "a3" "$C")
a4=$(val "a4" "$C")
a6=$(val "a6" "$C")
root_number=$(val "root_number" "$C")
parity=$(val "expected_rank_parity" "$C")
prank=$(val "proven_rank" "$C")
pfacs=$(val "prime_factors" "$C")

# harvest K3 invariants
kchi=$(val "euler_characteristic" "$K")
ksig=$(val "signature" "$K")
kc2=$(val "second_chern_class" "$K")
kpr=$(val "picard_rank_generic" "$K")
ktr=$(val "transcendental_lattice_rank" "$K")

# harvest fibration
gr=$(val "generic_mordell_weil_rank" "$F")
sr=$(val "special_fiber_rank" "$F")
rj=$(val "rank_increase" "$F")

# harvest points (x only)
mapfile -t X < <(grep -v "^[#]" "$P" | sed "/^$/d")

# hashes
hC=$(hashf "$C")
hK=$(hashf "$K")
hF=$(hashf "$F")
hP=$(hashf "$P")
hR=$(hashf "$R")
hW=$(hashf "$W")

# emit JSON deterministically
OUT=receipts/e29_receipt.json
> "$OUT"
printf "%s\n" "{" >> "$OUT"
printf "%s\n" "  \"schema\": \"tau_crystal.e29.v1\"," >> "$OUT"
printf "%s\n" "  \"ts\": \"$(iso)\"," >> "$OUT"
printf "%s\n" "  \"source_files\": [\"$C\",\"$K\",\"$F\",\"$P\",\"$R\",\"$W\"]," >> "$OUT"
printf "%s\n" "  \"hashes\": {" >> "$OUT"
printf "%s\n" "    \"$C\": \"$hC\"," >> "$OUT"
printf "%s\n" "    \"$K\": \"$hK\"," >> "$OUT"
printf "%s\n" "    \"$F\": \"$hF\"," >> "$OUT"
printf "%s\n" "    \"$P\": \"$hP\"," >> "$OUT"
printf "%s\n" "    \"$R\": \"$hR\"," >> "$OUT"
printf "%s\n" "    \"$W\": \"$hW\"" >> "$OUT"
printf "%s\n" "  }," >> "$OUT"
printf "%s\n" "  \"curve\": {" >> "$OUT"
printf "%s\n" "    \"model\": \"y^2 + x*y = x^3 + a4*x + a6\"," >> "$OUT"
printf "%s\n" "    \"a1\": \"$a1\", \"a2\": \"$a2\", \"a3\": \"$a3\"," >> "$OUT"
printf "%s\n" "    \"a4\": \"$a4\"," >> "$OUT"
printf "%s\n" "    \"a6\": \"$a6\"," >> "$OUT"
printf "%s\n" "    \"prime_factors\": \"$pfacs\"," >> "$OUT"
printf "%s\n" "    \"root_number\": \"$root_number\"," >> "$OUT"
printf "%s\n" "    \"expected_rank_parity\": \"$parity\"," >> "$OUT"
printf "%s\n" "    \"proven_rank\": \"$prank\"" >> "$OUT"
printf "%s\n" "  }," >> "$OUT"
printf "%s\n" "  \"k3\": { \"euler_characteristic\": \"$kchi\", \"signature\": \"$ksig\", \"second_chern_class\": \"$kc2\", \"picard_rank_generic\": \"$kpr\", \"transcendental_lattice_rank\": \"$ktr\" }," >> "$OUT"
printf "%s\n" "  \"fibration\": { \"generic_mordell_weil_rank\": \"$gr\", \"special_fiber_rank\": \"$sr\", \"rank_increase\": \"$rj\" }," >> "$OUT"
printf "%s\n" "  \"points\": {" >> "$OUT"
printf "%s"   "    \"x_coords\": [" >> "$OUT"
for i in "${!X[@]}"; do sep=", "; [ "$i" -eq 0 ] && sep=""; printf "%s\"%s\"" "$sep" "${X[$i]}" >> "$OUT"; done
printf "%s\n" "]" >> "$OUT"
printf "%s\n" "  }" >> "$OUT"
printf "%s\n" "}" >> "$OUT"

printf "%s\n" "$OUT"
