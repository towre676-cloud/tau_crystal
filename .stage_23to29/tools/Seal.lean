import Std
namespace Tools
namespace Seal

/-- Write UTFâ€‘8 (no BOM) text to a file. Lean strings are UTFâ€‘8 already,
so `putStr` is fine and does not inject a BOM. -/
def writeUtf8NoBom (path : String) (text : String) : IO Unit := do
  IO.FS.withFile path IO.FS.Mode.write fun h => h.putStr text

end Seal
end Tools

