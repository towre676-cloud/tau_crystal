#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022

die(){ printf "[err] %s\n" "$1" >&2; exit 1; }
sha(){ sha256sum "$1" | awk '{print $1}'; }
jget(){ k="$1"; f="$2"; awk -v k="\""k"\"" -F: '$0~k{v=$2;sub(/^[ \t]*/,"",v);gsub(/[",]/,"",v);print v;exit}' "$f"; }

merkle_dir(){
  d="$1"
  map="$(mktemp)"; trap 'rm -f "$map" "$tmp" "$tmp.new" 2>/dev/null || true' RETURN
  find "$d" -type f | LC_ALL=C sort > "$map"
  if [ ! -s "$map" ]; then echo 0; return; fi

  tmp="$(mktemp)"; : > "$tmp"
  while IFS= read -r f; do
    [ -f "$f" ] || continue
    sha "$f" >> "$tmp"
  done < "$map"

  while :; do
    n="$(wc -l < "$tmp")"
    if [ "$n" -le 1 ]; then cat "$tmp"; return; fi
    : > "$tmp.new"
    i=1
    while [ "$i" -le "$n" ]; do
      a="$(sed -n "${i}p" "$tmp")"
      j=$((i+1))
      if [ "$j" -le "$n" ]; then
        b="$(sed -n "${j}p" "$tmp")"
        printf "%s%s" "$a" "$b" | tr -d '\n' | sha256sum | awk '{print $1}' >> "$tmp.new"
      else
        printf "%s" "$a" | tr -d '\n' | sha256sum | awk '{print $1}' >> "$tmp.new"
      fi
      i=$((i+2))
    done
    mv -f "$tmp.new" "$tmp"
  done
}

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT" || die "bad root: $ROOT"

R="$(git config --get remote.origin.url | sed -E 's#git@github.com:#https://github.com/#; s#\.git$##')"
OWNER="$(echo "$R" | sed -E 's#https://github.com/([^/]+)/([^/]+).*#\1#')"
REPO="$(echo "$R" | sed -E 's#https://github.com/([^/]+)/([^/]+).*#\2#')"

ARCH=".tau_ledger/ci"
mkdir -p "$ARCH/github" "$ARCH/local" ".tau_ledger/debug"

usage(){ echo "ci_archive.sh {fetch N|index|verify|ingest-local}"; exit 1; }
[ $# -ge 1 ] || usage
cmd="$1"; shift || true

if [ "$cmd" = "fetch" ]; then
  N="${1:-10}"
  [ -n "${GITHUB_TOKEN:-}" ] || die "set GITHUB_TOKEN"
  API="https://api.github.com/repos/$OWNER/$REPO/actions/runs?per_page=$N"
  js="$ARCH/github/runs-$(date -u +%Y%m%dT%H%M%SZ).json"
  curl -fsSL -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" "$API" -o "$js" || die "fetch runs"

  grep -oE '"id":[[:space:]]*[0-9]+' "$js" | awk '{print $2}' | while read -r RID; do
    [ -n "$RID" ] || continue
    base="$ARCH/github/$RID"; mkdir -p "$base"
    curl -fsSL -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" "https://api.github.com/repos/$OWNER/$REPO/actions/runs/$RID" -o "$base/run.json" || true
    curl -fsSL -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" "https://api.github.com/repos/$OWNER/$REPO/actions/runs/$RID/artifacts" -o "$base/artifacts.json" || true
    curl -fsSL -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" -L "https://api.github.com/repos/$OWNER/$REPO/actions/runs/$RID/logs" -o "$base/logs.zip" || true
    if [ -s "$base/artifacts.json" ]; then
      grep -oE '"id":[[:space:]]*[0-9]+' "$base/artifacts.json" | awk '{print $2}' | while read -r AID; do
        curl -fsSL -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" -L "https://api.github.com/repos/$OWNER/$REPO/actions/artifacts/$AID/zip" -o "$base/artifact-$AID.zip" || true
      done
    fi
    printf "%s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ) fetched $RID" >> "$ARCH/fetch.log"
  done
  echo "[ok] fetched → $ARCH/github/"
  exit 0
fi

if [ "$cmd" = "index" ]; then
  JSONL="$ARCH/index.jsonl"
  CSV="$ARCH/index.csv"
  : > "$JSONL"
  echo "run_id,created_at,workflow,head_sha,conclusion,logs_sha,merkle_root,file_count" > "$CSV"

  for d in "$ARCH/github"/*; do
    [ -d "$d" ] || continue
    rid="$(basename "$d")"
    runj="$d/run.json"
    created=""; wf=""; head=""; concl=""
    if [ -s "$runj" ]; then
      created="$(jget created_at "$runj" || true)"
      wf="$(jget name "$runj" || true)"
      head="$(jget head_sha "$runj" || true)"
      concl="$(jget conclusion "$runj" || true)"
    fi
    logs_sha=""; [ -s "$d/logs.zip" ] && logs_sha="$(sha "$d/logs.zip")"
    files="$(find "$d" -type f | wc -l | awk '{print $1}')"
    root="$(merkle_dir "$d")"
    printf '%s\n' "{\"run_id\":\"$rid\",\"created_at\":\"$created\",\"workflow\":\"$wf\",\"head_sha\":\"$head\",\"conclusion\":\"$concl\",\"logs_sha\":\"$logs_sha\",\"merkle_root\":\"$root\",\"file_count\":$files}" >> "$JSONL"
    printf '%s,%s,%s,%s,%s,%s,%s,%s\n' "$rid" "$created" "$wf" "$head" "$concl" "$logs_sha" "$root" "$files" >> "$CSV"
  done

  for f in .tau_ledger/debug/diag-*.log; do
    [ -f "$f" ] || continue
    rid="$(basename "$f" .log)"
    ddir="$ARCH/local/$rid"; mkdir -p "$ddir"
    cp -n "$f" "$ddir/" || true
    root="$(merkle_dir "$ddir")"
    logs_sha="$(sha "$f")"
    created="$(printf '%s' "$rid" | sed 's/^diag-//; s/Z$/:00Z/')"
    printf '%s\n' "{\"run_id\":\"$rid\",\"created_at\":\"$created\",\"workflow\":\"local-diag\",\"head_sha\":\"\",\"conclusion\":\"\",\"logs_sha\":\"$logs_sha\",\"merkle_root\":\"$root\",\"file_count\":1}" >> "$JSONL"
    printf '%s,%s,%s,%s,%s,%s,%s,%s\n' "$rid" "$created" "local-diag" "" "" "$logs_sha" "$root" "1" >> "$CSV"
  done

  echo "[ok] index → $JSONL  and  $CSV"
  exit 0
fi

if [ "$cmd" = "verify" ]; then
  JSONL="$ARCH/index.jsonl"
  [ -s "$JSONL" ] || die "index missing; run index"
  ok=0; bad=0
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    rid="$(printf '%s' "$line" | awk -F"\"run_id\":\"" '{print $2}' | awk -F"\"" '{print $1}')"
    root="$(printf '%s' "$line" | awk -F"\"merkle_root\":\"" '{print $2}' | awk -F"\"" '{print $1}')"
    logs="$(printf '%s' "$line" | awk -F"\"logs_sha\":\"" '{print $2}' | awk -F"\"" '{print $1}')"
    d="$ARCH/github/$rid"; [ -d "$d" ] || d="$ARCH/local/$rid"
    [ -d "$d" ] || { echo "[FAIL] missing dir $rid"; bad=$((bad+1)); continue; }
    now="$(merkle_dir "$d")"
    if [ "$now" != "$root" ]; then echo "[FAIL] merkle $rid"; bad=$((bad+1)); continue; fi
    if [ -f "$d/logs.zip" ] && [ -n "$logs" ]; then
      [ "$(sha "$d/logs.zip")" = "$logs" ] || { echo "[FAIL] logs $rid"; bad=$((bad+1)); continue; }
    fi
    ok=$((ok+1))
  done < "$JSONL"
  echo "[ok] verified=$ok  bad=$bad"
  test "$bad" -eq 0
  exit $?
fi

if [ "$cmd" = "ingest-local" ]; then
  for f in .tau_ledger/debug/diag-*.log; do
    [ -f "$f" ] || continue
    rid="$(basename "$f" .log)"
    ddir="$ARCH/local/$rid"; mkdir -p "$ddir"
    cp -n "$f" "$ddir/" || true
  done
  echo "[ok] local diag logs ingested → $ARCH/local"
  exit 0
fi

usage
