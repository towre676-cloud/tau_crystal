#!/usr/bin/env bash
# progress_update.sh — upsert analysis/progress.tsv (strict 4 columns)
# usage: progress_update <organ> <status> [error_string]
set -euo pipefail; umask 022
progress="analysis/progress.tsv"
tmp="${progress}.tmp.$$"
organ="${1:?organ}"; status="${2:?status}"; err="${3:-}"
organ="$(printf "%s" "$organ" | tr '\t\r\n' ' ')"
status="$(printf "%s" "$status" | tr '\t\r\n' ' ')"
err="$(printf "%s" "$err"   | tr '\t\r\n' ' ')"
utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
[ -f "$progress" ] || echo -e "organ\tstatus\tlast_ok_utc\tlast_error" > "$progress"
awk -v OFS='\t' -v organ="$organ" -v status="$status" -v utc="$utc" -v err="$err" '
BEGIN{found=0}
NR==1{print $0; next}
{
  if($1==organ){
    found=1
    if(status=="ok"){print organ,status,utc,"-"}
    else{ lok=($3==""?"":$3); e=(err==""?($4==""?"-":$4):err); print organ,status,lok,e }
  } else {
    a1=$1; a2=$2; a3=($3==""? "":$3); a4=($4==""? "-":$4); print a1,a2,a3,a4
  }
}
END{
  if(found==0){
    if(status=="ok"){ print organ,status,utc,"-" }
    else{ print organ,status,"",(err==""? "-":err) }
  }
}' "$progress" > "$tmp" && mv "$tmp" "$progress"
echo "[PROGRESS] $organ -> $status"
