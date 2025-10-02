import Std
namespace Tau
/-- Arithmetic weighting ω(n)=φ(n)/σ(n) with safe fallbacks. -/
def gcd (a b : Nat) : Nat := Nat.gcd a b
def phi (n : Nat) : Nat :=
  if n ≤ 1 then 1 else
    let rec loop (p : Nat) (m : Nat) (acc : Nat) : Nat :=
      if p * p > m then acc * (if m > 1 then m - 1 else 1) else
        if m % p = 0 then
          let rec strip (q : Nat) (t : Nat) : Nat := if t % q = 0 then strip q (t / q) else t
          let m' := strip p m
          loop (p+1) m' (acc * (p - 1))
        else loop (p+1) m acc
    loop 2 n 1
def sigma (n : Nat) : Nat :=
  if n = 0 then 0 else
    let rec loop (p : Nat) (m : Nat) (acc : Nat) : Nat :=
      if p * p > m then acc * (if m > 1 then m + 1 else 1) else
        if m % p = 0 then
          let rec powerSum (q : Nat) (t : Nat) (pow : Nat) (sum : Nat) : (Nat × Nat) :=
            if t % q = 0 then powerSum q (t / q) (pow*q) (sum + pow*q) else (t, sum)
          let (m', s) := powerSum p m 1 1
          loop (p+1) m' (acc * s)
        else loop (p+1) m acc
    loop 2 n 1
def omega (n : Nat) : Rat :=
  let ph := phi n; let sg := sigma n
  if sg = 0 then 0 else (ph : Rat) / (sg : Rat)
def tauPulse (n : Nat) (kinetic : Rat) : Rat := (omega n) * kinetic
end Tau
