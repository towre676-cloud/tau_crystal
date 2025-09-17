#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/atlas/_intlib.sh

CURVE_LABEL="${1:?label}"
N="${2:?conductor}"
A1="${3:?}"; A2="${4:?}"; A3="${5:?}"; A4="${6:?}"; A6="${7:?}"

outdir="analysis/atlas/${CURVE_LABEL}"
mkdir -p "$outdir"

read -r B2 B4 B6 B8 DELTA < <(tau_invariants "$A1" "$A2" "$A3" "$A4" "$A6")

# Write ap panel
panel="$outdir/ap.tsv"
printf "p\ta_p\n" > "$panel"

hasse_ok=1
pcount=0
pmax=199

# simple prime generator up to pmax
is_prime(){ local n="$1" i; [ "$n" -lt 2 ] && return 1; for ((i=2;i*i<=n;i++)); do ((n%i))||return 1; done; return 0; }

for ((p=3; p<=pmax; p+=2)); do
  is_prime "$p" || continue
  # skip bad primes and p=2
  if [ $(( DELTA % p )) -eq 0 ]; then
    continue
  fi
  # exact #E(F_p)
  np=$(count_points_mod_p "$A1" "$A2" "$A3" "$A4" "$A6" "$p")
  ap=$(( p + 1 - np ))
  printf "%d\t%d\n" "$p" "$ap" >> "$panel"
  pcount=$((pcount+1))
  # Hasse: |a_p| <= 2 sqrt p
  # integer check: compare |a_p|^2 <= 4 p
  apabs=$(( ap<0 ? -ap : ap ))
  if [ $(( apabs*apabs )) -gt $((4*p)) ]; then hasse_ok=0; fi
done

# L-sum placeholders (we keep Tier-A honest: exact panel; numerics optional)
L1="nan"; Lhalf="nan"; tail="nan"

leaf="$outdir/leaf.json"
jq -n \
  --arg label "$CURVE_LABEL" \
  --argjson N "$N" \
  --argjson b2 "$B2" --argjson b4 "$B4" --argjson b6 "$B6" --argjson b8 "$B8" \
  --argjson delta "$DELTA" \
  --arg ap_path "$panel" \
  --argjson pcount "$pcount" \
  --argjson pmax "$pmax" \
  --arg hasse "$hasse_ok" \
  --arg L1 "$L1" --arg Lhalf "$Lhalf" --arg tail "$tail" \
  '{
     curve: {label: $label, conductor: $N, a: {a1:'"$A1"',a2:'"$A2"',a3:'"$A3"',a4:'"$A4"',a6:'"$A6"'}},
     invariants: {b2:$b2,b4:$b4,b6:$b6,b8:$b8,delta:$delta},
     panel: {path:$ap_path, primes_evaluated:$pcount, pmax:$pmax},
     checks: {hasse_ok: ($hasse=="1")},
     numerics: {L1:$L1, Lhalf:$Lhalf, tail_upper_bound:$tail}
   }' > "$leaf"

# Witness pack (text-only) for this curve
att="$outdir/attestation.json"
manifest="$outdir/manifest.json"
pack=".tau_ledger/discovery/witness-${N}-${CURVE_LABEL}-$(date -u +%Y%m%dT%H%M%SZ).tar.gz"

jq -n --arg uname "$(uname -a 2>/dev/null || echo unknown)" \
      --arg shell "$SHELL" \
      --arg runner "${GITHUB_RUN_ID:-}" \
      --arg sha "${GITHUB_SHA:-}" \
      '{uname:$uname, shell:$shell, ci:{github_run_id:$runner, commit:$sha}}' > "$att"

# manifest: file -> sha256
manifest_tmp="$(mktemp)"
for f in "$panel" "$leaf" "$att"; do
  if command -v sha256sum >/dev/null 2>&1; then
    printf '{"path":"%s","sha256":"%s"}\n' "$f" "$(sha256sum "$f" | awk '{print $1}')" >> "$manifest_tmp"
  else
    printf '{"path":"%s","sha256":"%s"}\n' "$f" "$(shasum -a256 "$f" | awk '{print $1}')" >> "$manifest_tmp"
  fi
done
jq -s '.' "$manifest_tmp" > "$manifest"
rm -f "$manifest_tmp"

# pack
tar -czf "$pack" -C "$outdir" "$(basename "$panel")" "$(basename "$leaf")" "$(basename "$att")" "$(basename "$manifest")"

echo "[atlas] built $CURVE_LABEL (N=$N) :: primes=$pcount hasse_ok=$hasse_ok"
