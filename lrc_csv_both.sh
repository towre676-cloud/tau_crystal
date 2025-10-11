#!/usr/bin/env sh
# Usage: ./lrc_csv_both.sh N a1 a2 ... ak
# Outputs one CSV row with both continuous and discrete results side-by-side.

N="$1"; shift
A_LIST="$*"
[ -z "$N" ] && { echo "err: need N and a_i" >&2; exit 1; }

cont_line=$(./lrc_csv.sh "$N" $A_LIST)                 || exit 2
disc_line=$(./lrc_csv_discrete.sh "$N" $A_LIST)        || exit 3

# parse continuous
IFS=, read -r cN ck calist c_sN c_sD c_mN c_mD c_OK <<EOF
$cont_line
EOF

# parse discrete
IFS=, read -r dN dk dalist d_sN d_sD d_mN d_mD d_OK <<EOF
$disc_line
EOF

# flag: does continuous s_den divide N?  (true discrete-realizable)
s_den_divides_N="NO"
if [ "$c_sD" -gt 0 ] && [ $(( N % c_sD )) -eq 0 ]; then
  s_den_divides_N="YES"
fi

agree_max="NO"
[ "$c_mN" = "$d_mN" ] && [ "$c_mD" = "$d_mD" ] && agree_max="YES"

# print header if env HEADER=1
if [ "${HEADER:-0}" = "1" ]; then
  echo "N,k,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,s_den_divides_N,agree_max"
fi

echo "$N,$ck,$calist,$c_sN,$c_sD,$c_mN,$c_mD,$c_OK,$d_sN,$d_sD,$d_mN,$d_mD,$d_OK,$s_den_divides_N,$agree_max"
