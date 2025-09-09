namespace TauCrystal
open TauCrystal

structure Manifest where
  soliton    : List Step
  toolchain  : String
  mathlibSha : String
  modules    : List Name
  digest     : ByteArray
deriving Repr, DecidableEq

axiom sha256 : ByteArray → ByteArray

def encode (m : Manifest) : ByteArray :=
  let s := toString m.soliton ++ "|" ++ m.toolchain ++ "|" ++ m.mathlibSha
  s.toUTF8

class CommitmentLaws where
  hom_concat :
    ∀ (a b : List Step) (tool math : String) (mods : List Name),
      let da := sha256 (encode { soliton := a, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
      let db := sha256 (encode { soliton := b, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
      let d_ab := sha256 (encode { soliton := a ++ b, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
      d_ab = sha256 (da ++ db)

theorem receipt_conserved [CommitmentLaws]
  (tool math : String) (mods : List Name) (a b : List Step) :
  let da := sha256 (encode { soliton := a, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
  let db := sha256 (encode { soliton := b, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
  let d_ab := sha256 (encode { soliton := a ++ b, toolchain := tool, mathlibSha := math, modules := mods, digest := ByteArray.empty })
  d_ab = sha256 (da ++ db) := by
  -- Provided by `CommitmentLaws.hom_concat`
  simpa using (CommitmentLaws.hom_concat a b tool math mods)

end TauCrystal
