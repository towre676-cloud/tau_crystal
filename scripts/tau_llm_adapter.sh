#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
tool="${1:-}"; inp="${2:-}"; out="${3:-}"
[ -n "$tool" ] && [ -n "$inp" ] && [ -n "$out" ] || { echo "[llm_adapter] usage: tau_llm_adapter.sh <tool> <input_path> <output_path>" >&2; exit 2; }
mkdir -p "$(dirname -- "$out")" 2>/dev/null || true
[ -f "$inp" ] || { echo "[llm_adapter] missing input: $inp" >&2; exit 3; }

normalize(){ tr -d "\r" | sed -Ee 's/[[:space:]]+/ /g' -e 's/^ //; s/ $//'; }
lower(){ tr '[:upper:]' '[:lower:]'; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | awk '{print $1}'; else openssl dgst -sha256 | awk '{print $2}'; fi; }
jesc(){ awk 'BEGIN{RS="";ORS=""}{gsub(/\\/,"\\\\");gsub(/"/,"\\\"");gsub(/\r/,"");gsub(/\t/,"\\t");gsub(/\n/,"\\n");printf "%s",$0}'; }

# --- input prep
in_raw=$(cat -- "$inp")
in_norm=$(printf "%s" "$in_raw" | normalize)
in_fold=$(printf "%s" "$in_norm" | lower)
h_in_raw=$(printf "%s" "$in_raw" | sha || true)
h_in_fold=$(printf "%s" "$in_fold" | sha || true)

# --- LLM step (or placeholder)
out_tmp=$(mktemp); trap 'rm -f "$out_tmp"' EXIT
if [ -n "${TAU_LLM_CMD:-}" ]; then
  printf "%s" "$in_raw" | eval "$TAU_LLM_CMD" > "$out_tmp" 2> "$out_tmp.err" || true
else
  printf "LLM adapter placeholder. tool=%s\nINPUT: %s\n" "$tool" "$in_norm" > "$out_tmp"
fi
out_raw=$(cat -- "$out_tmp")
out_norm=$(printf "%s" "$out_raw" | normalize)
out_fold=$(printf "%s" "$out_norm" | lower)
h_out_raw=$(printf "%s" "$out_raw" | sha || true)
h_out_fold=$(printf "%s" "$out_fold" | sha || true)

# --- semantic (prompt vs output)
fa=$(mktemp); fb=$(mktemp); trap 'rm -f "$fa" "$fb"' RETURN
printf "%s" "$in_norm"  > "$fa"
printf "%s" "$out_norm" > "$fb"
sem=$(bash scripts/tau_semantic.sh "$fa" "$fb" 2>/dev/null || echo '{"ok":false}')
cos_bow=$(printf "%s" "$sem" | sed -n 's/.*"cosine_bow":[ ]*\([0-9.]\+\).*/\1/p')
jac2=$(   printf "%s" "$sem" | sed -n 's/.*"jaccard_2gram":[ ]*\([0-9.]\+\).*/\1/p')
cos_emb=$(printf "%s" "$sem" | sed -n 's/.*"cosine_embed":[ ]*\([0-9.]\+\).*/\1/p' || true)
method="bow-only"; [ -n "${TAU_EMBED_CMD:-}" ] && method="embed+bow"

# --- consistency (paraphrases vs output text)
tmp_prompt=$(mktemp); tmp_text=$(mktemp); trap 'rm -f "$tmp_prompt" "$tmp_text"' RETURN
printf "%s" "$in_norm"  > "$tmp_prompt"
printf "%s" "$out_norm" > "$tmp_text"
cons=$(bash scripts/tau_consistency.sh "$tmp_prompt" "$tmp_text" 2>/dev/null || echo '{"ok":false}')

# --- write envelope (no behavior yet)
env_tmp=$(mktemp); trap 'rm -f "$env_tmp"' RETURN
{
  printf "{\n"
  printf "  \"tool\": \"%s\",\n" "$tool"
  printf "  \"input_sha256\": \"%s\",\n" "$h_in_raw"
  printf "  \"input_fold_sha256\": \"%s\",\n" "$h_in_fold"
  printf "  \"output_sha256\": \"%s\",\n" "$h_out_raw"
  printf "  \"output_fold_sha256\": \"%s\",\n" "$h_out_fold"
  printf "  \"semantic\": {\n"
  printf "    \"method\": \"%s\",\n" "$method"
  printf "    \"cosine_bow\": %s,\n" "${cos_bow:-0}"
  printf "    \"jaccard_2gram\": %s" "${jac2:-0}"
  [ -n "${cos_emb:-}" ] && printf ",\n    \"cosine_embed\": %s" "$cos_emb"
  printf "\n  },\n"
  printf "  \"output_text\": \"%s\"\n" "$(printf "%s" "$out_raw" | jesc)"
  printf "}\n"
} > "$env_tmp"

# --- run behavior checks on final envelope and inject
behv=$(bash scripts/tau_behavior.sh "$env_tmp" "${TAU_EXPECT_KEYS:-output_text}" 2>/dev/null || echo '{"ok":false}')

# --- final JSON (with behavior)
{
  printf "{\n"
  printf "  \"tool\": \"%s\",\n" "$tool"
  printf "  \"input_sha256\": \"%s\",\n" "$h_in_raw"
  printf "  \"input_fold_sha256\": \"%s\",\n" "$h_in_fold"
  printf "  \"output_sha256\": \"%s\",\n" "$h_out_raw"
  printf "  \"output_fold_sha256\": \"%s\",\n" "$h_out_fold"
  printf "  \"semantic\": {\n"
  printf "    \"method\": \"%s\",\n" "$method"
  printf "    \"cosine_bow\": %s,\n" "${cos_bow:-0}"
  printf "    \"jaccard_2gram\": %s" "${jac2:-0}"
  [ -n "${cos_emb:-}" ] && printf ",\n    \"cosine_embed\": %s" "$cos_emb"
  printf "\n  },\n"
  printf "  \"behavior\": {\n"
  printf "    \"consistency\": %s,\n" "$(printf "%s" "$cons" | tr -d "\n")"
  printf "    \"constraints\": %s\n" "$(printf "%s" "$behv" | tr -d "\n")"
  printf "  },\n"
  printf "  \"output_text\": \"%s\"\n" "$(printf "%s" "$out_raw" | jesc)"
  printf "}\n"
} > "$out"
