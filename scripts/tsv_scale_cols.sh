
#!/usr/bin/env bash
# tsv_scale_cols.sh <in.tsv> "<col1,col2,...>" <scale> <out.tsv>
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?}"; COLS_RAW="${2:?}"; SCALE="${3:?}"; OUT="${4:?}"
sed -i 's/\r$//' "$IN" 2>/dev/null || true
awk -v OFS="\t" -v SCALE="$SCALE" -v COLS_RAW="$COLS_RAW" '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
BEGIN{
  n=split(COLS_RAW, arr, / *, */);
  for(i=1;i<=n;i++){ want[canon(arr[i])]=1; }
}
NR==1{
  for(i=1;i<=NF;i++){ name[i]=canon($i); }
  print; next
}
{
  for(i=1;i<=NF;i++){
    if(want[name[i]]) { x=$i+0; printf("%.15g%s", x*SCALE, (i<NF?OFS:ORS)); }
    else              { printf("%s%s",    $i,     (i<NF?OFS:ORS)); }
  }
}
' "$IN" > "$OUT"

