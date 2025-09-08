import Lake
open Lake DSL

package «tau_crystal»

lean_lib «TauCrystal» where
  globs := #[.submodules `TauCrystal]

-- tau_crystal: lake script for manifest verification
script manifest (args) do
  let usage := "usage: lake manifest verify"
  if args.size == 1 && args.get! 0 == "verify" then
    let p := IO.Process.spawn {cmd := "python3", args := #["scripts/manifest_verify.py"]}
    let e ← p.wait
    if e == 0 then pure () else IO.Process.exit e
  else
    IO.eprintln usage
    IO.Process.exit 2
