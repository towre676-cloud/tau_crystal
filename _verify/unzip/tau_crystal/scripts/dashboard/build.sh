#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
root="$(pwd)"
atlas="analysis/atlas.jsonl"
build="build"
mkdir -p "$build/data" "$build/assets"

# 1) export committed atlas (LF normalize)
[ -s "$atlas" ] || { echo "[dash] missing $atlas" >&2; exit 4; }
tr -d '\r' < "$atlas" > "$build/data/atlas.jsonl"

# 2) tiny static app
cat > "$build/index.html" <<'HTML'
<!doctype html>
<meta charset="utf-8">
<title>τ-Crystal Atlas</title>
<body style="font-family:system-ui,Segoe UI,Roboto,Arial,sans-serif;margin:2rem;">
  <h1>τ-Crystal Atlas (verifiable)</h1>
  <pre id="meta"></pre>
  <table id="t" border="0" cellspacing="0" cellpadding="6">
    <thead><tr>
      <th align="left">type</th><th align="left">label</th><th align="left">ts</th><th align="left">extra</th>
    </tr></thead><tbody></tbody>
  </table>
  <script src="assets/app.js"></script>
</body>
HTML

cat > "$build/assets/app.js" <<'JS'
(async () => {
  const metaEl = document.getElementById('meta');
  const tbody  = document.querySelector('#t tbody');
  const m = await (await fetch('./_manifest.json')).json();
  metaEl.textContent = JSON.stringify(m, null, 2);
  const text = await (await fetch('./data/atlas.jsonl')).text();
  for (const L of text.trim().split(/\n/).slice(-200)) {
    let o={}; try{o=JSON.parse(L);}catch{continue;}
    const tr=document.createElement('tr');
    const extra=('mirror_ok'in o)?`mirror_ok=${o.mirror_ok}`:('agree'in o)?`agree=${o.agree}`:'';
    tr.innerHTML=`<td>${o.type||''}</td><td>${o.label||''}</td><td>${o.ts||''}</td><td>${extra}</td>`;
    tbody.appendChild(tr);
  }
})();
JS

# 3) hashes (absolute path to hasher)
data_hash="$("$root/scripts/meta/_sha256.sh" "$build/data/atlas.jsonl")"

tmp="$(mktemp)"
( cd "$build" && find . -type f -print0 | sort -z | while IFS= read -r -d '' f; do
    rel="${f#./}"; h="$("$root/scripts/meta/_sha256.sh" "$build/$rel")"
    printf "%s  %s\n" "$h" "$rel"
  done ) > "$tmp"
build_hash="$("$root/scripts/meta/_sha256.sh" "$tmp")"
rm -f "$tmp"

# 4) manifest (fixed key order)
ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || echo 1970-01-01T00:00:00Z)"
g="$(git rev-parse --short=12 HEAD 2>/dev/null || echo nogit)"
M="$build/_manifest.json"; : > "$M"
printf "%s" "{"                                   >> "$M"
printf "%s" "\"schema\":\"taucrystal/dashboard_manifest/v1\"," >> "$M"
printf "%s" "\"build_hash\":\"$build_hash\","     >> "$M"
printf "%s" "\"data_hash\":\"$data_hash\","       >> "$M"
printf "%s" "\"commit\":\"$g\","                  >> "$M"
printf "%s" "\"ts\":\"$ts\""                      >> "$M"
printf "%s\n" "}"                                 >> "$M"

echo "[dash] build ok data_hash=$data_hash build_hash=$build_hash"
