import Lake
open Lake DSL

package «spectral_kernel» where

lean_lib «Spectral» where
  srcDir := "Src"

lean_exe «plumbing» where
  root := `Spectral.plumbing
  supportInterpreter := true

lean_exe «face_plumbing» where
  root := `Spectral.face_plumbing
  supportInterpreter := true
