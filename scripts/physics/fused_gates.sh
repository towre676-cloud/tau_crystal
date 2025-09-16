#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1
EPS="${PHYSICS_EPS:-1e-6}"
OUT_CP="analysis/cp_residual.tsv"
OUT_PP="analysis/passport_sig.tsv"
OUT_AN="analysis/arith_nonce.tsv"
OUT_FUSED="analysis/fused_gates.json"
mkdir -p analysis .tau_ledger/chain

# 1) CP residual (make no-pairs neutral via STRICT=0 here)
set +e
OUT="$OUT_CP" EPS="$EPS" STRICT="${STRICT:-0}" bash scripts/tools/cp_residual_symm_verifier.sh analysis/morse_crit.tsv 1 3
cp_rc=$?
set -e
cp_residual=$(awk -v key=residual -v def=NaN -f scripts/tools/read_kv2.awk "$OUT_CP" 2>/dev/null)
cp_epsilon=$(awk  -v key=epsilon  -v def="$EPS" -f scripts/tools/read_kv2.awk "$OUT_CP" 2>/dev/null)
cp_pass=$(awk     -v key=pass     -v def=0    -f scripts/tools/read_kv2.awk "$OUT_CP" 2>/dev/null)
cp_bool=false; [ "$cp_pass" = "1" ] && cp_bool=true

# 2) Arithmetic nonce (Satake/Hecke → theta_min, gd_inv, nonce_hex)
bash scripts/physics/arith_nonce.sh "$OUT_AN" >/dev/null 2>&1 || true
[ -s analysis/hecke.tsv ] || bash scripts/langlands/emit_hecke_from_qexp.sh || true
[ -s analysis/satake_angles.tsv ] && : || { [ -s analysis/hecke.tsv ] && bash scripts/langlands/satake_from_hecke.sh || true; }
an_theta=$(awk -v key=theta_min -v def=NaN -f scripts/tools/read_kv2.awk "$OUT_AN" 2>/dev/null)
an_gdinv=$(awk -v key=gd_inv    -v def=NaN -f scripts/tools/read_kv2.awk "$OUT_AN" 2>/dev/null)
an_nonce=$(awk -v key=nonce_hex -v def=""  -f scripts/tools/read_kv2.awk "$OUT_AN" 2>/dev/null)

# 3) Ramanujan / endoscopic stability
ram_checked=0; ram_bad=0
if [ -s analysis/hecke.tsv ]; then set -- $(awk -f scripts/tools/ramanujan_stats.awk analysis/hecke.tsv); ram_checked="$1"; ram_bad="$2"; fi
endo_stable=1; [ "$ram_bad" -gt 0 ] && endo_stable=0
endo_bool=false; [ "$endo_stable" = "1" ] && endo_bool=true

# 4) Passport probe (deterministic NONCE_HEX when available)
set +e
NONCE_HEX="$an_nonce" OUT="$OUT_PP" bash scripts/physics/passport_probe.sh
pp_rc=$?
set -e
pp_nonce=$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk "$OUT_PP" 2>/dev/null)
pp_sig=$(awk   -v key=sig_hex   -v def="" -f scripts/tools/read_kv2.awk "$OUT_PP" 2>/dev/null)
pp_pub=$(awk   -v key=pub_hex   -v def="" -f scripts/tools/read_kv2.awk "$OUT_PP" 2>/dev/null)
pp_pass=$(awk  -v key=pass      -v def=0  -f scripts/tools/read_kv2.awk "$OUT_PP" 2>/dev/null)
pp_bool=false; [ "$pp_pass" = "1" ] && pp_bool=true

# 5) Laurent staircase (define defaults before set -u can bite)
laurent_pass=0; laurent_bool=false; L_real=; L_imag=; L_K=; L_q=
bash scripts/laurent/laurent_ring.sh || true
L_real=$(awk "END{print \$1}" analysis/laurent_ring.tsv 2>/dev/null || echo "")
L_imag=$(awk "END{print \$2}" analysis/laurent_ring.tsv 2>/dev/null || echo "")
L_K=$(awk   "END{print \$3}" analysis/laurent_ring.tsv 2>/dev/null || echo "")
L_q=$(awk   "END{print \$4}" analysis/laurent_ring.tsv 2>/dev/null || echo "")
m2=$(awk -v a="${L_real:-0}" -v b="${L_imag:-0}" "BEGIN{printf \"%.16g\", a*a+b*b}")
awk -v m="$m2" "BEGIN{d=m-1;if(d<0)d=-d; exit !(d<1e-12)}" >/dev/null 2>&1 && laurent_pass=1 || laurent_pass=0
[ "$laurent_pass" = "1" ] && laurent_bool=true || laurent_bool=false

# 6) Next-surface seed from nonce
seed="${pp_nonce:-$an_nonce}"; [ -z "$seed" ] && seed="00000000000000000000000000000000"
S_BASE=$(( 16#${seed:0:8} % 100000 ))
T_BASE=$(( 16#${seed:8:8} % 128 ))
{ printf "S_BASE\t%d\n" "$S_BASE"; printf "T_BASE\t%d\n" "$T_BASE"; } > analysis/next_surface.tsv

# 7) Fused pass (Laurent recorded but non-blocking for now)
fused_pass=0; [ "$cp_pass" = "1" ] && [ "$pp_pass" = "1" ] && fused_pass=1
if [ -n "${L_real:-}" ] && [ -n "${L_imag:-}" ] && [ "${L_real}" != "NaN" ] && [ "${L_imag}" != "NaN" ]; then
  [ "$laurent_pass" = "1" ] || fused_pass=0
fi
fused_bool=false; [ "$fused_pass" = "1" ] && fused_bool=true

# 8) Optional ts from chain tip
ts=""; [ -s ".tau_ledger/chain/CHAIN" ] && ts=$(tail -n1 .tau_ledger/chain/CHAIN | awk "{print \$1}" | tr -d "\r\n") || true

# 9) Emit canonical JSON (fixed order)
: > "$OUT_FUSED"
printf "%s" "{" >> "$OUT_FUSED"
printf "%s" "\"schema\":\"taucrystal/physics_fused_gates/v2\"" >> "$OUT_FUSED"
printf "%s" ",\"ts\":\"$ts\"" >> "$OUT_FUSED"
printf "%s" ",\"cp_residual\":{" >> "$OUT_FUSED"
printf "%s" "\"residual\":$cp_residual" >> "$OUT_FUSED"
printf "%s" ",\"epsilon\":$cp_epsilon" >> "$OUT_FUSED"
printf "%s" ",\"pass\":$cp_bool" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"arith_nonce\":{" >> "$OUT_FUSED"
printf "%s" "\"theta_min\":$an_theta" >> "$OUT_FUSED"
printf "%s" ",\"gd_inv\":$an_gdinv" >> "$OUT_FUSED"
printf "%s" ",\"nonce\":\"$an_nonce\"" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"passport\":{" >> "$OUT_FUSED"
printf "%s" "\"nonce\":\"$pp_nonce\"" >> "$OUT_FUSED"
printf "%s" ",\"sig\":\"$pp_sig\"" >> "$OUT_FUSED"
printf "%s" ",\"pk\":\"$pp_pub\"" >> "$OUT_FUSED"
printf "%s" ",\"pass\":$pp_bool" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"laurent\":{" >> "$OUT_FUSED"
printf "%s" "\"re\":${L_real:-0}" >> "$OUT_FUSED"
printf "%s" ",\"im\":${L_imag:-0}" >> "$OUT_FUSED"
printf "%s" ",\"K_k\":${L_K:-0}" >> "$OUT_FUSED"
printf "%s" ",\"q\":${L_q:-0}" >> "$OUT_FUSED"
printf "%s" ",\"pass\":$laurent_bool" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"ramanujan\":{" >> "$OUT_FUSED"
printf "%s" "\"checked\":%s" "$ram_checked" >> "$OUT_FUSED"
printf "%s" ",\"violations\":%s" "$ram_bad" >> "$OUT_FUSED"
printf "%s" ",\"endo_stable\":$endo_bool" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"next_surface\":{" >> "$OUT_FUSED"
printf "%s" "\"S_BASE\":%d" "$S_BASE" >> "$OUT_FUSED"
printf "%s" ",\"T_BASE\":%d" "$T_BASE" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"fused_pass\":$fused_bool" >> "$OUT_FUSED"
printf "%s\n" "}" >> "$OUT_FUSED"

# 10) Stamp sha256 and append CHAIN
if command -v sha256sum >/dev/null 2>&1; then shahex=$(sha256sum "$OUT_FUSED" | cut -d" " -f1);
elif command -v shasum >/dev/null 2>&1; then shahex=$(shasum -a 256 "$OUT_FUSED" | cut -d" " -f1);
else shahex=$(openssl dgst -sha256 "$OUT_FUSED" | awk "{print \$NF}"); fi
printf "%s  %s\n" "$shahex" "$OUT_FUSED" > "${OUT_FUSED}.sha256"
stamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf "%s\t%s\t%s\n" "$stamp" "$OUT_FUSED" "$shahex" >> .tau_ledger/chain/CHAIN

# 11) Exit fused status
[ "$fused_pass" = "1" ] && exit 0 || exit 8
