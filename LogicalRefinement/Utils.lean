import Init.Data.Nat

def Nat.le_lt_succ (p: n ≤ m): (n < succ m) := Nat.lt_succ_of_le p

def Nat.eq_zero_is_le_zero: (m ≤ 0) = (m = 0) := 
  propext (Iff.intro Nat.eq_zero_of_le_zero Nat.le_of_eq)

@[simp]
def Nat.max_zero_left: {m: Nat} -> Nat.max m 0 = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.eq_zero_is_le_zero] }

@[simp]
def Nat.max_zero_right: {m: Nat} -> Nat.max 0 m = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.zero_le] }

def Nat.max_gt_l {l r: Nat}: Nat.max l r ≥ l := sorry

def Nat.max_gt_r {l r: Nat}: Nat.max l r ≥ r := sorry

def Nat.max_lt_l {l r: Nat}: l ≤ Nat.max l r := sorry
 
def Nat.max_lt_r {l r: Nat}: r ≤ Nat.max l r := sorry

def Nat.max_val_l {l r: Nat}: r ≤ l -> Nat.max l r = l := sorry

def Nat.max_val_r {l r: Nat}: l ≤ r -> Nat.max l r = r := sorry

def Nat.max_le_split: (Nat.max l r ≤ m) = (l ≤ m ∧ r ≤ m) := by {
  apply propext;
  apply Iff.intro;
  case a.mp =>
    intro Hm
    exact ⟨Nat.le_trans max_lt_l Hm, Nat.le_trans max_lt_r Hm⟩
  case a.mpr =>
    intro ⟨Hl, Hr⟩
    cases Nat.le_total l r with
    | inl Hlr => 
      rw [Nat.max_val_r Hlr]
      apply Hr
    | inr Hrl =>
      rw [Nat.max_val_l Hrl]
      apply Hl
}

private def Nat.succ_right: n + Nat.succ l = Nat.succ (n + l) := rfl

def Nat.succ_le_succ_is_le: (succ n ≤ succ m) = (n ≤ m) :=
  propext (Iff.intro Nat.le_of_succ_le_succ Nat.succ_le_succ)

def Nat.zero_sub: {n: Nat} -> 0 - n = 0
  | 0 => rfl
  | Nat.succ n => by {
    rw [Nat.sub_succ].
    rw [zero_sub].
    rfl
  }

def Nat.zero_le_true: (0 ≤ n) = True :=
  propext (Iff.intro (λ _ => True.intro) (λ _ => Nat.zero_le _))

def Nat.le_sub_is_le_add: {l n m: Nat} -> (n - l ≤ m) = (n ≤ m + l) := by {
  intros l.
  induction l with
  | zero => rfl
  | succ l I => intros n. cases n with
    | zero => intros m.
      rw [Nat.zero_sub]. 
      rw [Nat.zero_le_true].
      rw [Nat.zero_le_true]
    | succ n => intros m.
      rw [Nat.succ_sub_succ_eq_sub].
      rw [Nat.succ_right].
      rw [Nat.succ_le_succ_is_le].
      apply I
}