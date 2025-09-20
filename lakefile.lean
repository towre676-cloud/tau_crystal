import Lake
open Lake DSL

package tau

-- optional: mathlib for proofs lib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

lean_lib Tau
lean_lib TauProofs

@[default_target]
lean_exe «prove_v2» where
  root := `Tau.ProveV2
