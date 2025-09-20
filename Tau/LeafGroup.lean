namespace Tau

abbrev LeafID := String
abbrev LeafGroup := LeafID → Int

def leafGroupZero : LeafGroup := fun _ => 0
def leafGroupAdd  (f g : LeafGroup) : LeafGroup := fun x => f x + g x
def leafGroupNeg  (f   : LeafGroup) : LeafGroup := fun x => - (f x)

def leafGroupL1Norm (f : LeafGroup) (support : List LeafID) : Nat :=
  support.foldl (fun acc x => acc + Int.natAbs (f x)) 0

def leafGroupIsZero (f : LeafGroup) (support : List LeafID) : Bool :=
  support.all (fun x => f x = 0)

instance : Zero LeafGroup where zero := leafGroupZero
instance : Add  LeafGroup where add  := leafGroupAdd
instance : Neg  LeafGroup where neg  := leafGroupNeg

end Tau
