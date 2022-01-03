import Init.Data.Nat

def Nat.eq_zero_is_le_zero: (m ≤ 0) = (m = 0) := propext (
  Iff.intro
  Nat.eq_zero_of_le_zero
  (by { sorry })
)

def max_zero_left: (m: Nat) -> Nat.max m 0 = m
  | 0 => rfl
  | Nat.succ n => by { simp only [Nat.max, Nat.eq_zero_is_le_zero]; simp }

def max_zero_right: (m: Nat) -> Nat.max 0 m = m
  | 0 => rfl
  | Nat.succ n => by { simp only [Nat.max, Nat.zero_le]; simp }