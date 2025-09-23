#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022

# Usage: make_morpho_pair.sh A_front.jpg A_left.jpg A_right.jpg B_front.jpg B_left.jpg B_right.jpg
A_F="${1:-}"; A_L="${2:-}"; A_R="${3:-}"; B_F="${4:-}"; B_L="${5:-}"; B_R="${6:-}"

sha256_any(){
  f="$1"; [ -f "$f" ] || { echo "NA"; return 0; }
  if command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 "$f" | awk "{print \$2}";
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$f" | awk "{print \$1}";
  elif command -v certutil >/dev/null 2>&1; then certutil -hashfile "$f" SHA256 | awk "NR==2{print}";
  else echo "NA"; fi
}

stamp_utc(){ date -u +%%Y-%%m-%%dT%%H:%%M:%%SZ; }

H_A_F=$(sha256_any "$A_F"); H_A_L=$(sha256_any "$A_L"); H_A_R=$(sha256_any "$A_R")
H_B_F=$(sha256_any "$B_F"); H_B_L=$(sha256_any "$B_L"); H_B_R=$(sha256_any "$B_R")
ROOT_INPUT="${H_A_F}${H_A_L}${H_A_R}${H_B_F}${H_B_L}${H_B_R}"
ROOT=$(printf "%s" "$ROOT_INPUT" | { if command -v openssl >/dev/null 2>&1; then openssl dgst -sha256 -binary | openssl dgst -sha256 | awk "{print \$2}"; else printf "%s" "$ROOT_INPUT"; fi; })
NOW=$(stamp_utc)

OUT_J=".tau_ledger/discovery/morpho_signature_pair.json"
OUT_R=".tau_ledger/discovery/morpho_signature_pair.receipt.tsv"
: > "$OUT_J"
printf "%s" "{" >> "$OUT_J"
printf "%s" "\"version\":\"1.0\",\"created_utc\":\"$NOW\",\"root\":\"$ROOT\"," | sed "s/^/{/" > /tmp/_mjson.tmp
: > "$OUT_J"
printf "%s" "{" >> "$OUT_J"
printf "%s" "\"version\":\"1.0\",\"created_utc\":\"$NOW\",\"root\":\"$ROOT\"," >> "$OUT_J"
printf "%s" "\"atlas\":{\"midline_lock\":true,\"nasal_geodesic_lock\":true}," >> "$OUT_J"
printf "%s" "\"invariants\":{\"nasion_axis\":true,\"intercanthal_level\":true,\"zygion_chord\":true,\"dorsal_curvature\":true}," >> "$OUT_J"
printf "%s" "\"coefficients\":{\"mandibular_projection\":null,\"envelope_descent\":null}," >> "$OUT_J"
printf "%s" "\"subjects\":{" >> "$OUT_J"
printf "%s" "\"A\":{\"role\":\"flat_plane_ClassI_basis\",\"files\":{\"front\":{\"path\":\"${A_F:-}\",\"sha256\":\"$H_A_F\"},\"left\":{\"path\":\"${A_L:-}\",\"sha256\":\"$H_A_L\"},\"right\":{\"path\":\"${A_R:-}\",\"sha256\":\"$H_A_R\"}}}," >> "$OUT_J"
printf "%s" "\"B\":{\"role\":\"convex_plane_mature_counterpart\",\"files\":{\"front\":{\"path\":\"${B_F:-}\",\"sha256\":\"$H_B_F\"},\"left\":{\"path\":\"${B_L:-}\",\"sha256\":\"$H_B_L\"},\"right\":{\"path\":\"${B_R:-}\",\"sha256\":\"$H_B_R\"}}}" >> "$OUT_J"
printf "%s" "}," >> "$OUT_J"
printf "%s" "\"notes\":\"Joint quiet‑scaffold atlas with two orthogonal flows: sagittal base (Class I↔Class II) and aging envelope; coefficients left null for downstream estimator to fill; JSON is receipt‑bound via root.\"" >> "$OUT_J"
printf "%s\n" "}" >> "$OUT_J"

: > "$OUT_R"
printf "%s\n" "CREATED=$NOW" >> "$OUT_R"
printf "%s\n" "TOOL=morpho_pair_v1" >> "$OUT_R"
printf "%s\n" "ROOT=$ROOT" >> "$OUT_R"
printf "%s\n" "A_FRONT_SHA256=$H_A_F" >> "$OUT_R"
printf "%s\n" "A_LEFT_SHA256=$H_A_L" >> "$OUT_R"
printf "%s\n" "A_RIGHT_SHA256=$H_A_R" >> "$OUT_R"
printf "%s\n" "B_FRONT_SHA256=$H_B_F" >> "$OUT_R"
printf "%s\n" "B_LEFT_SHA256=$H_B_L" >> "$OUT_R"
printf "%s\n" "B_RIGHT_SHA256=$H_B_R" >> "$OUT_R"
printf "%s\n" "JSON=morpho_signature_pair.json" >> "$OUT_R"
printf "%s\n" "STATUS=OK" >> "$OUT_R"
echo "wrote $OUT_J and $OUT_R"
