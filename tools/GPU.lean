import Std
namespace Tools
namespace GPU

structure Certificate where
  matrixDigest : String
  primes : List Nat
  r0 : Nat
  r1 : Nat
  obstructionDim : Int
deriving Repr

structure Config where
  useGPU : Bool
  linkageLengths : List Float
deriving Repr

def build (_cfg : Config) : Certificate :=
  { matrixDigest := "sha256:stub0000"
  , primes := [2000003, 2000029, 2000039]
  , r0 := 2, r1 := 5, obstructionDim := 3 }

end GPU
end Tools
