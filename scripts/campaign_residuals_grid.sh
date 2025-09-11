#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
stamp=$(date -u +%Y%m%d_%H%M%SZ)
root="campaigns/residuals_$stamp"; mkdir -p "$root" analysis
bounds='"theta12_min":20,"theta12_max":40,"theta13_min":5,"theta13_max":12,"theta23_min":35,"theta23_max":55,"delta_min":-10,"delta_max":10'
sumtol='1e-3'
templates=("TM1" "TM2" "Z2_mu_tau_with_CP" "Z2_mu_tau_reflection")
betas=("0.0" "10.0" "20.0")
theta13s=("7.5" "9.0" "10.5")
ledger="$root/ledger.jsonl"; : > "$ledger"

hash_json(){ python3 - "$1" <<'PY'; import sys,hashlib,json; d=json.load(open(sys.argv[1],'r',encoding='utf-8')); print(hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":")).encode()).hexdigest()); PY }

for tmpl in "${templates[@]}"; do
  for th13 in "${theta13s[@]}"; do
    for b in "${betas[@]}"; do
      cname="$root/${tmpl}_th${th13}_b${b}.contract.json"
      rname="$root/${tmpl}_th${th13}_b${b}.request.json"
      oname="analysis/${tmpl}_th${th13}_b${b}.out.json"
      # build contract
      printf '{ "templates": { "Ge":"Z3_TBM", "Gnu":"%s" }, "parameters": { "theta13_deg": %s, "beta_deg": %s }, "bounds": { %s }, "sum_rule_tol": %s, "assumptions": { "taken_as_given": ["Mapping not derived; testing %s pattern."], "to_test": ["preserved column witness","angle windows"] } }\n' "$tmpl" "$th13" "$b" "$bounds" "$sumtol" "$tmpl" > "$cname"
      cinp_hash=$(hash_json "$cname")

      # optional TM pre-gate
      if [[ "$tmpl" == TM1 || "$tmpl" == TM2 ]]; then
        rsum="$root/${tmpl}_th${th13}_b${b}.sumrule.request.json"
        osum="analysis/${tmpl}_th${th13}_b${b}.sumrule.out.json"
        printf '{ "tool":"tm_sumrule_gate", "input_path":"%s", "output_path":"%s" }\n' "$cname" "$osum" > "$rsum"
        rsum_hash=$(hash_json <(printf '%s' "$(cat "$rsum")") 2>/dev/null || echo "0")
        bash scripts/tau_exec.sh "$rsum" > "${osum%.out.json}.receipt.json" || true
        echo "{\"ts\":\"$stamp\",\"kind\":\"tm_sumrule\",\"template\":\"$tmpl\",\"theta13\":$th13,\"beta\":$b,\"contract\":\"$cname\",\"contract_sha\":\"$cinp_hash\",\"request\":\"$rsum\",\"request_sha\":\"$rsum_hash\"}" >> "$ledger"
        # if pre-gate failed, skip full run
        if ! grep -q '"ok":true' "${osum%.out.json}.receipt.json"; then
          continue
        fi
      fi

      # full residual verifier request (uses your existing cp_residual_symm_verifier tool)
      printf '{ "tool":"cp_residual_symm_verifier", "input_path":"%s", "output_path":"%s" }\n' "$cname" "$oname" > "$rname"
      rreq_hash=$(hash_json <(printf '%s' "$(cat "$rname")") 2>/dev/null || echo "0")
      bash scripts/tau_exec.sh "$rname" > "${oname%.out.json}.receipt.json" || true
      echo "{\"ts\":\"$stamp\",\"kind\":\"residual_run\",\"template\":\"$tmpl\",\"theta13\":$th13,\"beta\":$b,\"contract\":\"$cname\",\"contract_sha\":\"$cinp_hash\",\"request\":\"$rname\",\"request_sha\":\"$rreq_hash\"}" >> "$ledger"
    done
  done
done

# build campaign summary from receipts
python3 - "$root" <<'PY' > "$root/summary.json"
import sys,glob,json
camp=sys.argv[1]; rows=[]
for p in sorted(glob.glob('analysis/*receipt.json')):
    try: j=json.load(open(p,'r',encoding='utf-8'))
    except: continue
    rows.append({
        "file": p.replace("\\","/"),
        "ok": j.get("ok"),
        "templates": j.get("templates",{}),
        "parameters": j.get("parameters",{}),
        "angles": j.get("angles",{}),
        "witness": j.get("witness",{}),
        "input_sha256": j.get("input_sha256"),
        "request_sha256": j.get("request_sha256"),
    })
print(json.dumps({"campaign": camp, "results": rows}, separators=(",",":")))
PY

# human README from summary
CAMP="$root" python3 - <<'PY'
import os,json
camp=os.environ["CAMP"]; s=json.load(open(os.path.join(camp,"summary.json"),encoding="utf-8"))
def fmt(x): return f"{x:.2f}" if isinstance(x,(int,float)) else ("—" if (x in (None,{},[])) else str(x))
lines=["# Residual Symmetry Grid (τ-Crystal receipts)","","Windows: θ₁₂∈[20°,40°], θ₁₃∈[5°,12°], θ₂₃∈[35°,55°], |δ|≤10°.","","| ok | template | params | θ12 | θ13 | θ23 | δ | witnesses | receipt |","|:--:|:--|:--|:--:|:--:|:--:|:--:|:--|:--|"]
for r in s["results"]:
    ok="✅" if r.get("ok") else "❌"
    T=r.get("templates") or {}; P=r.get("parameters") or {}; A=r.get("angles") or {}; W=r.get("witness") or {}
    tname=f"{T.get('Ge','—')},{T.get('Gnu','—')}" if T else "—"
    params=", ".join(f"{k}={v}" for k,v in P.items()) or "—"
    wfail=[k for k,v in W.items() if v is False]
    wtxt="fail:"+",".join(wfail) if wfail else ("all✓" if W else "—")
    rec=(r.get("file") or "—").replace("\\","/")
    lines.append(f"| {ok} | {tname} | {params} | {fmt(A.get('theta12_deg'))} | {fmt(A.get('theta13_deg'))} | {fmt(A.get('theta23_deg'))} | {fmt(A.get('delta_deg'))} | {wtxt} | `{rec}` |")
open(os.path.join(camp,"README.md"),"w",encoding="utf-8").write("\n".join(lines))
PY

# bundle + manifest
tar -czf "$root/artifacts.tgz" -C "$root" README.md summary.json ledger.jsonl 2>/dev/null || true
( cd "$root" && { printf "SHA256  FILE\n" > MANIFEST.sha256; sha256sum README.md summary.json ledger.jsonl artifacts.tgz 2>/dev/null >> MANIFEST.sha256; } )
echo "$root"
