import Std.Data.List.Basic

namespace Tau

abbrev LeafID := String
abbrev LeafGroup := LeafID → Int

def leafGroupZero : LeafGroup := fun _ => 0
def leafGroupAdd (f g : LeafGroup) : LeafGroup := fun x => f x + g x
def leafGroupNeg (f : LeafGroup) : LeafGroup := fun x => - (f x)
def leafGroupSmul (n : Int) (f : LeafGroup) : LeafGroup := fun x => n * f x

def leafGroupL1Norm (f : LeafGroup) (support : List LeafID) : Nat :=
  support.foldl (fun acc x => acc + Int.natAbs (f x)) 0

def leafGroupSupport (f : LeafGroup) (cands : List LeafID) : List LeafID :=
  cands.filter (fun x => f x ≠ 0)

def singleLeaf (id : LeafID) : LeafGroup := fun x => if x = id then 1 else 0

def leafGroupIsZero (f : LeafGroup) (support : List LeafID) : Bool :=
  support.all (fun x => f x = 0)

instance : Zero LeafGroup where zero := leafGroupZero
instance : Add LeafGroup where add := leafGroupAdd
instance : Neg LeafGroup where neg := leafGroupNeg

@[simp] theorem add_apply (f g : LeafGroup) (x : LeafID) :
  (f + g) x = f x + g x := rfl
@[simp] theorem zero_apply (x : LeafID) : (0 : LeafGroup) x = 0 := rfl
@[simp] theorem neg_apply (f : LeafGroup) (x : LeafID) : (-f) x = -(f x) := rfl

end Tau
