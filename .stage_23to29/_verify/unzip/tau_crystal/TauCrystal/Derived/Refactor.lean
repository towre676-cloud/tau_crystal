/-!
Derived refactoring scaffold: chain complexes of receipts, homotopies, and Ext¹ as obstruction to refactorings.
-/
namespace TauCrystal.Derived

structure Receipt where
  ctx : String
  bytes : ByteArray

structure Chain where
  deg : Int → List Receipt
  d   : Int → (List Receipt → List Receipt)

structure Homotopy where
  K : Int → (List Receipt → List Receipt)

def isChainMap (C D : Chain) (f : Int → (List Receipt → List Receipt)) : Prop :=
  ∀ n, (D.d n) (f n (C.deg n)) = f (n-1) (C.d n (C.deg n))

def homotopic (C D : Chain) (f g : Int → (List Receipt → List Receipt)) : Prop :=
  ∃ H : Homotopy, ∀ n, (g n (C.deg n)) = (f n (C.deg n)) ++ (D.d n (H.K n (C.deg n))) ++ (H.K (n-1) (C.d n (C.deg n)))

axiom Ext1_obstructs (C D : Chain) : Prop

end TauCrystal.Derived
