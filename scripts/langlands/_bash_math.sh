#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
MICRO=${MICRO:-1000000}
dec_to_micro(){ v="${1:-0}"; case "$v" in "" ) v="0";; .* ) v="0${v}";; esac; A="${v%%.*}"; B="${v#*.}"; B="${B%%[!0-9]*}"; echo $(( 10#${A}*MICRO + 10#${B} )); }
clamp_micro(){ x="$1"; [ "$x" -lt 0 ] && x=0; [ "$x" -gt "$MICRO" ] && x="$MICRO"; echo "$x"; }
isqrt(){ n="${1:-0}"; [ "$n" -le 0 ] && { echo 0; return; }; x="$n"; y=$(( (x + 1) / 2 )); while [ "$y" -lt "$x" ]; do x="$y"; y=$(( (x + n / x) / 2 )); done; echo "$x"; }
abs(){ a="$1"; case "$a" in -*) echo "${a#-}";; *) echo "$a";; esac; }
read_kv(){ f="$1"; k="$2"; awk -v k="$k" -F= '$1==k{gsub(/\r/,"",$2); gsub(/^[[:space:]]+|[[:space:]]+$/,"",$2); print $2}' "$f" 2>/dev/null | head -n1; }
