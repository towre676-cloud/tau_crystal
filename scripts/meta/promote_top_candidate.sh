#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
R="receipts/genus/top_candidate.txt"; [ -s "$R" ] || { echo "no top candidate. run scan_candidates.sh" >&2; exit 2; }
T=$(cut -d, -f1 "$R")
JR="receipts/${T}_receipt.json"
[ -s "$JR" ] || { > "$JR"; printf "%s\n" "{" >> "$JR"; printf "%s\n" "  \"schema\":\"tau_crystal.curve_arith.v1\"," >> "$JR"; printf "%s\n" "  \"curve\":{\"model\":\"y^2 + x*y = x^3 + a4*x + a6\",\"a1\":\"1\",\"a2\":\"0\",\"a3\":\"0\",\"a4\":\"\",\"a6\":\"\",\"prime_factors\":\"\",\"root_number\":\"-1\",\"expected_rank_parity\":\"odd\",\"proven_rank\":\"\"}," >> "$JR"; printf "%s\n" "  \"fibration\":{\"generic_mordell_weil_rank\":\"\",\"special_fiber_rank\":\"\",\"rank_increase\":\"\"}," >> "$JR"; printf "%s\n" "  \"points\":{\"x_coords\":[]}" >> "$JR"; printf "%s\n" "}" >> "$JR"; }
JG="receipts/genus/${T}_observation.json"; [ -s "$JG" ] || { echo "missing $JG" >&2; exit 3; }
SC="scripts/meta/${T}_compare.sh"
> "$SC"
printf "%s\n" "#!/usr/bin/env bash" >> "$SC"
printf "%s\n" ". \"$(dirname "$0")/../safe/_env.sh\"" >> "$SC"
printf "%s\n" "set -e" >> "$SC"
printf "%s\n" "cd \"$HOME/Desktop/tau_crystal/tau_crystal\" || exit 1" >> "$SC"
printf "%s\n" "JR=\"receipts/${T}_receipt.json\"; JG=\"receipts/genus/${T}_observation.json\"" >> "$SC"
printf "%s\n" "[ -s \"$JR\" ] && [ -s \"$JG\" ] || { echo missing receipts >&2; exit 2; }" >> "$SC"
printf "%s\n" "pyr(){ python scripts/safe/json_read.py \"\$1\" \"\$JR\"; }" >> "$SC"
printf "%s\n" "pyg(){ python scripts/safe/json_read.py \"\$1\" \"\$JG\"; }" >> "$SC"
printf "%s\n" "rz=\$(pyg twisted.zero_modes); rg=\$(pyg generic.zero_modes); w=\$(pyr curve.root_number)" >> "$SC"
printf "%s\n" "[ \"\$w\" = \"-1\" ] && [ -n \"\$rz\" ] && [ -n \"\$rg\" ] && [ \"\$rz\" -gt \"\$rg\" ] && { echo CONSISTENT; exit 0; } || { echo INCONSISTENT \"w=\$w generic=\$rg twisted=\$rz\"; exit 1; }" >> "$SC"
chmod +x "$SC"; printf "%s\n" "$T"
