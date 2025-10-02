import Lake
open Lake DSL

package tau

lean_lib Tau
lean_lib TauProofs

@[default_target]
lean_exe «prove_v2» where
  root := `Tau.ProveV2
