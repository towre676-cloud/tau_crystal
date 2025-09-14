/-!
ReceiptCategory: categorical scaffold for τ‑Crystal receipts.
This is a minimal structure; project‑local instances can refine equalities and coherence.
-/

namespace TauCrystal

structure ReceiptCategory where
  Obj  : Type
  Hom  : Obj → Obj → Type
  id   : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_left  : {X Y : Obj} → (f : Hom X Y) → comp (id X) f = f
  id_right : {X Y : Obj} → (f : Hom X Y) → comp f (id Y) = f
  assoc    : {W X Y Z : Obj} → (f : Hom W X) → (g : Hom X Y) → (h : Hom Y Z) →
              comp f (comp g h) = comp (comp f g) h

/-!
Intent: instantiate with Obj := ReceiptContext, Hom := CanonicalReceipt.
Placeholders below keep the file compiling until those types are available in scope.
-/
structure ReceiptContext where
  dummy : Unit := ()

structure CanonicalReceipt (A B : ReceiptContext) where
  unit : Unit := ()

def ReceiptCategory.default : ReceiptCategory where
  Obj  := ReceiptContext
  Hom  := fun _ _ => CanonicalReceipt
  id   := fun X => { unit := () }
  comp := fun f g => { unit := () }
  id_left  := by intro; rfl
  id_right := by intro; rfl
  assoc    := by intro; rfl

end TauCrystal
