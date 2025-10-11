#!/usr/bin/env sh
# Usage: ./lrc_csv.sh N a1 a2 ... ak
# Emits: N,k,"a1 a2 ... ak",s_num,s_den,max_num,max_den,OK

if [ "$#" -lt 2 ]; then echo "Usage: $0 N a1 a2 ... ak" >&2; exit 1; fi
N="$1"; shift
A_LIST="$*"
# count k (number of a_i)
K=$(printf '%s\n' "$A_LIST" | awk '{print NF}')

OUT="$(./lrc_tiny.sh "$N" $A_LIST)"
# strip CR just in case
OUT="$(printf '%s\n' "$OUT" | tr -d '\r')"

# parse line 1: "max f(s) = p/q at s = r/s"
set -- $(printf '%s\n' "$OUT" | awk 'NR==1{ if (match($0,/max f\(s\) = ([0-9]+)\/([0-9]+) at s = ([0-9]+)\/([0-9]+)/,m)) print m[1],m[2],m[3],m[4]; }')
MAX_NUM="$1"; MAX_DEN="$2"; S_NUM="$3"; S_DEN="$4"

# parse OK from line 3
OK=$(printf '%s\n' "$OUT" | awk '/LRC satisfied\?/{print $NF}')

# fallback guards
[ -z "$MAX_NUM" ] && MAX_NUM=0
[ -z "$MAX_DEN" ] && MAX_DEN=1
[ -z "$S_NUM" ]   && S_NUM=0
[ -z "$S_DEN" ]   && S_DEN=1
[ -z "$OK" ]      && OK=UNKNOWN

echo "$N,$K,\"$A_LIST\",$S_NUM,$S_DEN,$MAX_NUM,$MAX_DEN,$OK"
