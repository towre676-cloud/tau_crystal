#!/usr/bin/env sh
# Usage: ./lrc_check_family.sh lrc_family_results.csv
CSV="${1:-lrc_family_results.csv}"
awk -F, 'NR==1{next}
{
  N=$1; k=$2; sN=$4; sD=$5; mN=$6; mD=$7; ok=$8
  good = (sN==1 && sD==N && mN==1 && mD==N && ok=="YES")
  if(!good){print "FAIL:",$0}else{pass++}
}
END{print "PASS =",pass,"rows OK"}' "$CSV"
