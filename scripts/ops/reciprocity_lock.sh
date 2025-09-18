#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

sha256(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; return; fi
  if command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; return; fi
  openssl dgst -sha256 "$1" 2>/dev/null | awk "{print \$NF}"
}

iso_now(){ date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || python - <<PY\nimport datetime;print(datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"))\nPY
}

fail(){ echo "[lock] $*" >&2; exit 7; }

[ -s analysis/reciprocity_best.env ]   || fail "missing analysis/reciprocity_best.env"
[ -s analysis/reciprocity_second.env ] || fail "missing analysis/reciprocity_second.env"

. analysis/reciprocity_best.env   2>/dev/null || true
. analysis/reciprocity_second.env 2>/dev/null || true

BS="${BEST_S_MICRO:-}";  BT="${BEST_T_MICRO:-}"
SS="${SECOND_S_MICRO:-}"; ST="${SECOND_T_MICRO:-}"
[ -n "$BS" ] && [ -n "$BT" ] || fail "BEST_* not set";
[ -n "$SS" ] && [ -n "$ST" ] || fail "SECOND_* not set";

best_pair="$BS $BT"; second_pair="$SS $ST"
[ "$best_pair" = "$second_pair" ] || fail "selector outputs disagree: best=[$best_pair] second=[$second_pair]"

sel_hash=$(printf "%s\n" "$best_pair" | { if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | cut -d" " -f1; else openssl dgst -sha256 2>/dev/null|awk "{print \$NF}"; fi; })
b_sha=$(sha256 analysis/reciprocity_best.env)
s_sha=$(sha256 analysis/reciprocity_second.env)

ts=$(iso_now); root=".tau_ledger/reciprocity"; mkdir -p "$root"
out="$root/dual_witness_${ts//[:]/-}.json"
: > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/dual_witness/v1\"," >> "$out"
printf "%s\n" "  \"timestamp\":\"$ts\"," >> "$out"
printf "%s\n" "  \"pair\":{\"s_micro\":\"$BS\",\"t_micro\":\"$BT\"}," >> "$out"
printf "%s\n" "  \"selector_hash\":\"$sel_hash\"," >> "$out"
printf "%s\n" "  \"files\":{\"best_env_sha256\":\"$b_sha\",\"second_env_sha256\":\"$s_sha\"}" >> "$out"
printf "%s\n" "}" >> "$out"

atlas="analysis/atlas.jsonl"; mkdir -p "$(dirname "$atlas")"; touch "$atlas"
printf "%s\n" "{\"type\":\"WITNESS_PAIR\",\"ts\":\"$ts\",\"s_micro\":\"$BS\",\"t_micro\":\"$BT\",\"selector_hash\":\"$sel_hash\",\"best_sha\":\"$b_sha\",\"second_sha\":\"$s_sha\"}" >> "$atlas"

echo "[lock] ok: pair=($BS,$BT) sel_hash=$sel_hash";
exit 0
