import Std

namespace TauCrystal

abbrev F := Float
abbrev Vec := Array F

structure LinOp where
  n      : Nat
  apply  : Vec → Vec      -- y := A x
  center : F := 0.0       -- for scaling to [-1,1]
  scale  : F := 1.0       -- y := (A - c I)/s

private def vmap (x : Vec) (f : F → F) : Vec := x.map f

private def vlin (a : F) (x : Vec) (b : F) (y : Vec) : Vec :=
  Id.run do
    let mut out : Vec := mkArray x.size 0.0
    for i in [:x.size] do
      out := out.set! i (a * x[i]! + b * y[i]!)
    out

def chebApply (op : LinOp) (coeffs : List F) (x : Vec) : Vec :=
  match coeffs with
  | [] => mkArray x.size 0.0
  | a0 :: cs =>
    -- u0 = (a0/2) * x
    let u0 := vmap x (fun xi => (a0 / 2.0) * xi)
    if cs.isEmpty then
      u0
    else
      -- u1 = a1 * T1(Â)x = a1 * (Â x)
      let a1 := cs.head!
      let t0 := x
      let t1 := op.apply x
      let u1 := vlin a1 t1 1.0 u0
      -- Clenshaw-like recurrence for remaining coeffs
      let rec loop (acc : Vec) (t_k : Vec) (t_km1 : Vec) (rest : List F) : Vec :=
        match rest with
        | [] => acc
        | a :: rs =>
          -- T_{k+1}(Â)x = 2 Â T_k x − T_{k−1} x
          let t_kp1 := vlin 2.0 (op.apply t_k) (-1.0) t_km1
          let acc'  := vlin a t_kp1 1.0 acc
          loop acc' t_kp1 t_k rs
      loop u1 t1 t0 cs.tail!

def degreeForTol (eps : F) : Nat :=
  let e := if eps ≤ 1e-12 then 1e-12 else eps
  let m := (Float.log (1.0 / e) / Float.log 1.5)  -- coarse dial; we’ll replace with d_s
  Nat.ofFloat (Float.ceil m)

end TauCrystal
