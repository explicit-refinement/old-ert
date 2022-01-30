import Init.Data.Nat

def Nat.le_lt_succ (p: n ≤ m): (n < succ m) := Nat.lt_succ_of_le p

def Nat.eq_zero_is_le_zero: (m ≤ 0) = (m = 0) := 
  propext (Iff.intro Nat.eq_zero_of_le_zero Nat.le_of_eq)

def max_zero_left: (m: Nat) -> Nat.max m 0 = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.eq_zero_is_le_zero] }

def max_zero_right: (m: Nat) -> Nat.max 0 m = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.zero_le] }