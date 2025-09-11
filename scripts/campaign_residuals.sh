#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
stamp=$(date -u +%Y%m%d_%H%M%SZ)
root="campaigns/residuals_$stamp"; mkdir -p "$root" analysis
bounds='"theta12_min":20,"theta12_max":40,"theta13_min":5,"theta13_max":12,"theta23_min":35,"theta23_max":55,"delta_min":-10,"delta_max":10'
declare -a schemes=("TM1" "TM2")
declare -a betas=("7.5" "10.0" "12.5")
for sch in "${schemes[@]}"; do
  for b in "${betas[@]}"; do
    C="$root/${sch}_b${b}.contract.json"
    O="analysis/${sch}_b${b}.receipt.json"
    printf '{ "templates": { "Ge":"Z3_TBM", "Gnu":"%s" }, "parameters": { "theta13_deg": 9.0, "beta_deg": %s }, "bounds": { %s }, "assumptions": { "taken_as_given": ["Mapping not derived; testing %s pattern."], "to_test": ["preserved column witness","angle windows"] } }\n' "$sch" "$b" "$bounds" "$sch" > "$C"
    R="$root/${sch}_b${b}.request.json"
    printf '{ "tool":"cp_residual_symm_verifier", "input_path":"%s", "output_path":"analysis/%s_b%s.out.json" }\n' "$C" "$sch" "$b" > "$R"
    bash scripts/tau_exec.sh "$R" > "$O" || true
    echo "ran $R -> $O"
  done
done
# quick summary
python3 - "$root" <<'PY'
import sys,json,glob
folder=sys.argv[1]
out=[]
for rec in glob.glob("analysis/*receipt.json"):
    j=json.load(open(rec,'r',encoding='utf-8'))
    out.append({"file":rec,"ok":j.get("ok"),"angles":j.get("angles"),"templates":j.get("templates",{}),"params":j.get("parameters",{}),"witness":j.get("witness",{})})
json.dump({"campaign":folder,"results":out}, open(folder+"/summary.json","w",encoding="utf-8"), separators=(",",":"))
print(folder+"/summary.json")
PY
