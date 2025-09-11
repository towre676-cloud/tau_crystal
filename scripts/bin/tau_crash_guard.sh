#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

root="$PWD"
sh_files=$(git ls-files "*.sh" 2>/dev/null || true)
fail=0
warn(){ printf "%s\n" "$*" >&2; }
die(){ printf "[err] %s\n" "$*" >&2; exit 1; }

printf "%s\n" "[guard] τ-Crystal crash analytics (no heredocs, history-safe)"

# 1) Detect files with CRLF
crlf_list=$(printf "%s\n" "$sh_files" | xargs -r -I{} bash -c 'grep -Il $'\r' "{}" >/dev/null 2>&1 || exit 0; grep -l $'\r' "{}" 2>/dev/null || true')
if [ -n "$crlf_list" ]; then
  warn "[guard] CRLF endings detected in:"
  printf "%s\n" "$crlf_list" >&2
  fail=1
fi

# 2) Heredoc use (disallowed)
heredoc_hits=$(printf "%s\n" "$sh_files" | xargs -r grep -nE '<<-?[A-Za-z_"]' || true)
if [ -n "$heredoc_hits" ]; then
  warn "[guard] heredocs found:"
  printf "%s\n" "$heredoc_hits" >&2
  fail=1
fi

# 3) Missing `set +H` in prologue (history expansion hazard)
missing_setH=""
for f in $sh_files; do
  head -n 5 "$f" | grep -q "set +H" || missing_setH="$missing_setH"$'\n'"$f"
done
missing_setH=$(printf "%s\n" "$missing_setH" | sed "/^$/d" || true)
if [ -n "$missing_setH" ]; then
  warn "[guard] scripts missing set +H in first 5 lines:"
  printf "%s\n" "$missing_setH" >&2
  fail=1
fi

# 4) Stray repeated bangs that can crash an interactive paste
bang_hits=$(printf "%s\n" "$sh_files" | xargs -r grep -nE '!!!!|echo[[:space:]].*!$' || true)
if [ -n "$bang_hits" ]; then
  warn "[guard] suspicious bang patterns (history-expansion risk):"
  printf "%s\n" "$bang_hits" >&2
  fail=1
fi

# 5) Python in .sh (language leakage)
py_in_sh=$(printf "%s\n" "$sh_files" | xargs -r grep -nE '^\s*(from[[:space:]].*import|import[[:space:]][A-Za-z_])' || true)
if [ -n "$py_in_sh" ]; then
  warn "[guard] python-style imports inside .sh:"
  printf "%s\n" "$py_in_sh" >&2
  fail=1
fi

# 6) Literal crash tokens seen in this thread
weird=$(printf "%s\n" "$sh_files" | xargs -r grep -nE 'CABCE|CACBE' || true)
if [ -n "$weird" ]; then
  warn "[guard] weird tokens (CABCE/CACBE) present:"
  printf "%s\n" "$weird" >&2
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  printf "%s\n" "[guard] clean: no heredocs, no history hazards, no language leakage, no CRLF."
else
  exit 1
fi
