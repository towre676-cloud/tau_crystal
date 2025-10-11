#!/usr/bin/env sh
# Usage: ./lrc_compare_continuous_vs_discrete.sh annotated_continuous.csv > compare.csv
# Reads continuous CSV (with header), recomputes DISCRETE result, and reports differences.

IN="${1:-lrc_random_results_annotated.csv}"
echo "N,k,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,s_den_divides_N,agree_max"

tail -n +2 "$IN" | while IFS=, read -r N k alist sN sD mN mD OK rest; do
  # clean a_list quotes -> space list
  a_clean=$(printf "%s" "$alist" | sed 's/^"//; s/"$//')
  # compute discrete
  disc_line=$(./lrc_csv_discrete.sh "$N" $a_clean)
  # parse discrete fields
  IFS=, read -r dN dk dalist dsN dsD dmN dmD dOK <<EOF
$disc_line
EOF

  # flags
  sdiv="NO"; [ $((sD % N)) -eq 0 ] && sdiv="YES"   # (continuous s_den divides N)? useful quick signal
  agree="NO"; [ "$mN" = "$dmN" ] && [ "$mD" = "$dmD" ] && agree="YES"

  echo "$N,$k,$alist,$sN,$sD,$mN,$mD,$OK,$dsN,$dsD,$dmN,$dmD,$dOK,$sdiv,$agree"
done
