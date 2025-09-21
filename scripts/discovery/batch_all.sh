#!/usr/bin/env bash
set +H; umask 022
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

ROOT_IN="analysis/morpho/input"
ROOT_OUT="analysis/morpho/output"
ROOT_IDX="analysis/morpho/index"
INGEST="scripts/morpho/face15_ingest.sh"
METRICS="scripts/morpho/face15_metrics.sh"
SCANNER="scripts/discovery/modular_curve_scan.sh"   # optional
MODDIR=".tau_ledger/discovery/modcurves"
HJ=".tau_ledger/hysteresis/box-CM-D23/hysteresis.json"

mkdir -p "$ROOT_OUT" "$ROOT_IDX" ".tau_ledger/faces" "$MODDIR" ".tau_ledger/discovery"

# normalize CRLF on runner if present
for f in "$INGEST" "$METRICS" "$SCANNER"; do
  [ -f "$f" ] || continue
  awk '{sub(/\r$/,"");print}' "$f" > "$f.tmp" && mv "$f.tmp" "$f"
  chmod +x "$f" || true
done

STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
REC=".tau_ledger/faces/face-batch-$STAMP.tsv"
printf 'when\t%s\n' "$STAMP" > "$REC"
printf 'hysteresis\t%s\n' "$HJ" >> "$REC"

SUBJS="$(find "$ROOT_IN" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' 2>/dev/null | awk '!/^(Cody_A|Mother_A)$/')"

if [ -n "$SUBJS" ]; then
  for S in $SUBJS; do
    IN="$ROOT_IN/$S"; OUT="$ROOT_OUT/$S"; IDX="$ROOT_IDX/${S}.tsv"
    if [ -x "$INGEST" ]; then "$INGEST" "$IN" "$OUT" || echo "[[note]] ingest failed for $S"; fi
    if [ -x "$METRICS" ]; then "$METRICS" "$OUT" "$IDX" || echo "[[note]] metrics failed for $S"; fi
    [ -s "$IDX" ] || printf "harmony_v2\tna\n" > "$IDX"
    printf 'subject\t%s\nmorpho\t%s\n' "$S" "$IDX" >> "$REC"
  done

  if [ -x "$SCANNER" ]; then
    SS="$(printf "%s" "$SUBJS" | tr '\n' ' ')"
    [ -n "$SS" ] && "$SCANNER" --subjects "$SS" --out "$MODDIR" || true
  fi
  for S in $SUBJS; do MC="$MODDIR/$S.json"; [ -s "$MC" ] && printf 'modcurve\t%s\n' "$MC" >> "$REC"; done
else
  echo "[[ok]] no non-canonical subjects under $ROOT_IN"
fi

echo "[[receipt]] $REC"

SCOREFILE=".tau_ledger/discovery/face_scores-$STAMP.tsv"
printf "subject\tharmony_v2\tlevel\tscore\n" > "$SCOREFILE"

FOUND=0
for MC in "$MODDIR"/*.json; do
  [ -f "$MC" ] || continue
  FOUND=1
  S="$(basename "$MC" .json)"
  IDX="$ROOT_IDX/$S.tsv"
  H="$(awk -F'\t' 'tolower($1)=="harmony_v2"{print $2; exit}' "$IDX" 2>/dev/null)"; [ -n "$H" ] || H="na"
  L="$(tr -d '\r\\' < "$MC" | tr -c '[:alnum:]' ' ' | awk '{for(i=1;i<=NF;i++) if(tolower($i)=="level"){print $(i+1); exit}}')"; [[ "$L" =~ ^[0-9]+$ ]] || L=0
  HN="$(awk -v x="$H" 'BEGIN{if(x+0<=0){print 0}else{y=x/100.0; if(y<0)y=0; if(y>1)y=1; printf("%.6f",y)}}')"
  LN="$(awk -v l="$L" 'BEGIN{if(l+0<=0){print 0}else{y=l/50.0; if(y<0)y=0; if(y>1)y=1; printf("%.6f",y)}}')"
  SC="$(awk -v a="$HN" -v b="$LN" 'BEGIN{printf("%.6f",a*b)}')"
  printf "%s\t%s\t%s\t%s\n" "$S" "$H" "$L" "$SC" >> "$SCOREFILE"
done

if [ "$FOUND" -eq 1 ]; then
  { read h; printf "%s\n" "$h"; sort -t$'\t' -k4,4gr; } < "$SCOREFILE" > "$SCOREFILE.sorted" && mv "$SCOREFILE.sorted" "$SCOREFILE"
fi

echo "[[scores]] $SCOREFILE"

PLOT=".tau_ledger/discovery/face_scores_plot-$STAMP.html"
{
  echo '<!doctype html><meta charset="utf-8"><title>τ-Crystal Face Scores</title>'
  echo '<style>body{font-family:system-ui,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:24px}'
  echo 'svg{max-width:100%;height:auto}.pt{fill:rgba(0,0,0,.6)}.pt:hover{stroke:#000;stroke-width:1}'
  echo '.axis text{font-size:12px;fill:#333}.axis line,.axis path{stroke:#888;shape-rendering:crispEdges}</style>'
  echo '<h2>Harmony vs Level (size = Score)</h2><svg id="viz" width="900" height="520"></svg>'
  echo '<script id="tsv" type="text/plain">'; cat "$SCOREFILE"; echo '</script>'
  echo '<script>(function(){const raw=document.getElementById("tsv").textContent.trim().split(/\\r?\\n/);raw.shift();'
  echo 'const rows=raw.map(l=>l.split("\\t")).map(c=>({s:c[0],h:+c[1],l:+c[2],sc:+c[3]})).filter(d=>!isNaN(d.l)&&!isNaN(d.h));'
  echo 'const W=900,H=520,M={l:60,r:20,t:20,b:50},ns="http://www.w3.org/2000/svg",svg=document.getElementById("viz");'
  echo 'function el(n,a){const e=document.createElementNS(ns,n);for(const k in a)e.setAttribute(k,a[k]);svg.appendChild(e);return e;}'
  echo 'function sx(v){const xMin=0,xMax=Math.max(10,...rows.map(d=>d.l));return M.l+(v-xMin)*(W-M.l-M.r)/(xMax-0||1)}'
  echo 'function sy(v){const yMin=Math.min(70,...rows.map(d=>d.h)),yMax=Math.max(90,...rows.map(d=>d.h));return H-M.b-(v-yMin)*(H-M.t-M.b)/(yMax-yMin||1)}'
  echo 'function ss(v){const m=Math.max(0.2,...rows.map(d=>d.sc));return 4+20*(v/m)}'
  echo 'for(let v=0;v<=Math.max(10,...rows.map(d=>d.l));v++) el("line",{x1:sx(v),y1:H-M.b,x2:sx(v),y2:H-M.b+6,stroke:"#666"});'
  echo 'for(let v=Math.floor(Math.min(70,...rows.map(d=>d.h)));v<=Math.max(90,...rows.map(d=>d.h));v++) el("line",{x1:M.l-6,y1:sy(v),x2:M.l,y2:sy(v),stroke:"#666"});'
  echo 'el("text",{x:W/2,y:H-10,"text-anchor":"middle"}).textContent="Level";el("text",{x:16,y:20,transform:"rotate(-90 16,20)"}).textContent="Harmony v2";'
  echo 'const tip=document.createElement("div");tip.style="position:absolute;pointer-events:none;background:#000;color:#fff;padding:6px 8px;border-radius:6px;font:12px/1.2 system-ui;opacity:0;transform:translate(-50%,-140%)";document.body.appendChild(tip);'
  echo 'svg.addEventListener("mousemove",e=>{tip.style.left=e.pageX+"px";tip.style.top=e.pageY+"px"});'
  echo 'rows.forEach(d=>{const c=el("circle",{class:"pt",cx:sx(d.l),cy:sy(d.h),r:ss(d.sc)});c.addEventListener("mouseenter",()=>{tip.innerHTML=`<b>${d.s}</b><br>Harmony ${d.h}<br>Level ${d.l}<br>Score ${d.sc}`;tip.style.opacity=1});c.addEventListener("mouseleave",()=>{tip.style.opacity=0})});})();</script>'
} > "$PLOT"

echo "[[plot]] $PLOT"
