import Std
namespace Tools
namespace TauEmit

structure Dial where
  baseline : Float
  threshold : Float
deriving Repr

def emit (obs : Int) (tau : Float) (_dial : Dial) : IO PUnit := do
  IO.println s!"tau-pulse: obs={obs} at Ãâ€ž={tau}"

end TauEmit
end Tools
