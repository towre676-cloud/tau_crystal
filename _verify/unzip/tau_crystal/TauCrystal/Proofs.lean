namespace TauCrystal

structure TauClock where
  t : Nat
deriving Repr

def tick (c : TauClock) : TauClock := { t := c.t.succ }

theorem tick_strict (c : TauClock) : c.t < (tick c).t := by
  simpa [tick] using Nat.lt_succ_self c.t

theorem tick_monotone (c : TauClock) : c.t ≤ (tick c).t := by
  exact Nat.le_of_lt (tick_strict c)

end TauCrystal
