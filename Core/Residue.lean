import Std
namespace Core
namespace Residue

structure Residue where
  obs : Int
deriving Repr

def add (a b : Residue) : Residue := { obs := a.obs + b.obs }

end Residue
end Core

