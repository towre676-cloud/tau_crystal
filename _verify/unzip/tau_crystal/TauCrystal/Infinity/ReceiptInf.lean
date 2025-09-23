/-!
Higher receipts scaffold (stub): contexts, receipts, and a simple composition.
-/
namespace TauCrystal.Infinity
structure Ctx where id : String
structure Rec (A B : Ctx) where bytes : ByteArray
def compose {A B C : Ctx} (f : Rec A B) (g : Rec B C) : Rec A C := { bytes := f.bytes ++ g.bytes }
end TauCrystal.Infinity
