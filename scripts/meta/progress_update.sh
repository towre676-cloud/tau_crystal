#!/usr/bin/env bash
# progress_update.sh  — upsert analysis/progress.tsv
# usage: progress_update <organ> <status> [error_string]
set -euo pipefail; umask 022
progress="analysis/progress.tsv"
tmp="${progress}.tmp.$$"
organ="${1:?organ}"; status="${2:?status}"
err="${3:-}"
utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# ensure header
if [ ! -f "$progress" ]; then
  echo -e "organ\tstatus\tlast_ok_utc\tlast_error" > "$progress"
fi

# read existing, rewrite the one row
awk -v OFS='\t' -v organ="$organ" -v status="$status" -v utc="$utc" -v err="$err" '
BEGIN{found=0}
NR==1{print $0; next}
{
  if($1==organ){
    found=1
    if(status=="ok"){
      print organ, status, utc, "-"
    }else{
      # keep last_ok_utc as-is
      print organ, status, $3, (err==""? $4 : err)
    }
  } else {
    print $0
  }
}
END{
  if(found==0){
    if(status=="ok"){ print organ, status, utc, "-" }
    else{ print organ, status, "", (err==""? "-" : err) }
  }
}
' "$progress" > "$tmp" && mv "$tmp" "$progress"
echo "[PROGRESS] $organ -> $status"
