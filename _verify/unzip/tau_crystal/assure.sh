#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# ---- locate lake ----
LAKE="${HOME}/.elan/bin/lake.exe"
if [[ ! -x "$LAKE" ]]; then
  if command -v lake >/dev/null 2>&1; then LAKE="lake"; else
    echo "ERROR: lake.exe not found at ~/.elan/bin and 'lake' not on PATH." >&2
    exit 1
  fi
fi

expected_q_raw=("0" "0.5" "1" "2")
normalize_q(){ echo "$1" | sed -E 's/^([0-9]+)\.0$/\1/'; }

run_one() {
  local runid="$1" outfile="$2"
  rm -f "$outfile"
  "$LAKE" update >/dev/null 2>&1 || true
  "$LAKE" build >/dev/null
  "$LAKE" exe tau_crystal -- --tau 1.25 --q 0,0.5,1,2 --run-id "$runid" --out "$outfile" --audit true
}

# PowerShell/pwsh-based JSON normalizer (no -Args; pass via env var)
normalize_manifest() {
  if command -v pwsh >/dev/null 2>&1; then
    MF="$1" pwsh -NoProfile -Command '
      $m = Get-Content -Raw -LiteralPath $env:MF | ConvertFrom-Json
      $m.PSObject.Properties.Remove("run_id") | Out-Null
      $m.PSObject.Properties.Remove("out")    | Out-Null
      $names   = ($m.PSObject.Properties | % Name | Sort-Object)
      $ordered = [ordered]@{}
      foreach($k in $names){ $ordered[$k] = $m.$k }
      $ordered | ConvertTo-Json -Compress
    '
  else
    MF="$1" powershell -NoProfile -Command '
      $m = Get-Content -Raw -LiteralPath $env:MF | ConvertFrom-Json
      $m.PSObject.Properties.Remove("run_id") | Out-Null
      $m.PSObject.Properties.Remove("out")    | Out-Null
      $names   = ($m.PSObject.Properties | % Name | Sort-Object)
      $ordered = [ordered]@{}
      foreach($k in $names){ $ordered[$k] = $m.$k }
      $ordered | ConvertTo-Json -Compress
    '
  fi
}

# -------- pass 1 --------
s1="$(run_one "assure-1" "manifest_assure1.json" | cat; true)"
[[ -f manifest_assure1.json ]] || { echo "manifest_assure1.json missing" >&2; exit 1; }

obs_cert="$(echo "$s1" | sed -nE 's/.*obstructionDim := ([0-9]+).*/\1/p' | head -n1)"
obs_pulse="$(echo "$s1" | sed -nE 's/.*tau-pulse:[[:space:]]*obs=([0-9]+).*/\1/p' | head -n1)"
[[ -n "$obs_cert"  ]] || { echo "Missing 'cert:' line with obstructionDim." >&2; echo "$s1"; exit 1; }
[[ -n "$obs_pulse" ]] || { echo "Missing 'tau-pulse:' line." >&2;              echo "$s1"; exit 1; }
[[ "$obs_cert" == "$obs_pulse" ]] || { echo "Mismatch: cert obs=$obs_cert vs pulse obs=$obs_pulse" >&2; echo "$s1"; exit 1; }
echo "✓ obs match ($obs_cert)"

mapfile -t seen_q < <(echo "$s1" \
  | grep -oE 'qCRO:[[:space:]]*q=[0-9]+(\.[0-9]+)?' \
  | sed -E 's/.*q=([0-9]+(\.[0-9]+)?)/\1/' \
  | while read -r q; do normalize_q "$q"; done \
  | sort -u)
expected_q=(); for q in "${expected_q_raw[@]}"; do expected_q+=("$(normalize_q "$q")"); done
missing=()
for q in "${expected_q[@]}"; do
  found=0; for s in "${seen_q[@]:-}"; do [[ "$s" == "$q" ]] && found=1 && break; done
  [[ $found -eq 0 ]] && missing+=("$q")
done
[[ ${#missing[@]} -eq 0 ]] || { echo "qCRO coverage incomplete. expected=[${expected_q[*]}] seen=[${seen_q[*]-}]" >&2; echo "$s1"; exit 1; }
echo "✓ qCRO coverage for q=[${expected_q[*]}]"

# -------- pass 2 --------
s2="$(run_one "assure-2" "manifest_assure2.json" | cat; true)"
[[ -f manifest_assure2.json ]] || { echo "manifest_assure2.json missing" >&2; exit 1; }

m1n="$(normalize_manifest manifest_assure1.json | tr -d '\r\n\t ')"
m2n="$(normalize_manifest manifest_assure2.json | tr -d '\r\n\t ')"
if [[ "$m1n" != "$m2n" ]]; then
  echo "Non-deterministic manifest (ignoring run_id/out)" >&2
  diff -u <(echo "$m1n") <(echo "$m2n") || true
  exit 1
fi
echo "✓ deterministic manifest (ignoring run_id/out)"

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  elif command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'
  elif command -v certutil  >/dev/null 2>&1; then certutil -hashfile "$1" SHA256 | sed -n '2p' | tr -d '\r'
  else echo "no-sha256"
  fi
}
h1="$(sha256 manifest_assure1.json)"; h2="$(sha256 manifest_assure2.json)"
[[ "$h1" != "no-sha256" ]] && echo "SHA256(manifest_assure1.json) = $h1"
[[ "$h2" != "no-sha256" ]] && echo "SHA256(manifest_assure2.json) = $h2"

echo
echo "ALL CHECKS PASSED."
