import Init.Data.Nat

def Nat.le_lt_succ (p: n ≤ m): (n < succ m) := Nat.lt_succ_of_le p

def Nat.eq_zero_is_le_zero: (m ≤ 0) = (m = 0) := 
  propext (Iff.intro Nat.eq_zero_of_le_zero Nat.le_of_eq)

def Nat.succ_le_is_le: (succ m ≤ succ n) = (m ≤ n) := 
  propext (Iff.intro Nat.le_of_succ_le_succ Nat.succ_le_succ)

@[simp]
def Nat.max_zero_left: {m: Nat} -> Nat.max m 0 = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.eq_zero_is_le_zero] }

@[simp]
def Nat.max_zero_right: {m: Nat} -> Nat.max 0 m = m
  | 0 => rfl
  | Nat.succ n => by { simp [Nat.max, Nat.zero_le] }

@[simp]
def Nat.max_bin_succ: Nat.max (Nat.succ l) (Nat.succ r) = Nat.succ (Nat.max l r) := by {
  unfold Nat.max
  cases (Nat.decLe l r).em with
  | inl Ht => 
    rw [if_pos Ht]
    rw [if_pos (Nat.succ_le_succ Ht)]
  | inr Ht => 
    rw [if_neg Ht]
    rw [if_neg (λAht => Ht (Nat.le_of_succ_le_succ Aht))]
}

@[simp]
def Nat.max_idempotent {l: Nat}: Nat.max l l = l := by {
  unfold Nat.max
  rw [if_pos]
  apply Nat.le_refl
}

def Nat.max_val_l {l r: Nat} (p: r ≤ l): Nat.max l r = l := by {
  unfold Nat.max
  cases (Nat.decLe l r).em with
  | inl Ht =>
    rw [if_pos Ht]
    exact Nat.le_antisymm p Ht
  | inr Hf =>
    rw [if_neg Hf]
}

def Nat.max_val_r {l r: Nat} (p: l ≤ r): Nat.max l r = r := by {
  unfold Nat.max
  rw [if_pos]
  exact p
}

def Nat.max_lt_l {l r: Nat}: l ≤ Nat.max l r := by {
  unfold Nat.max
  cases (Nat.decLe l r).em with
  | inl Ht =>
    rw [if_pos Ht]
    apply Ht
  | inr Hf =>
    rw [if_neg Hf]
    apply Nat.le_refl
}
 
def Nat.max_lt_r {l r: Nat}: r ≤ Nat.max l r := by {
  unfold Nat.max
  cases (Nat.decLe l r).em with
  | inl Ht =>
    rw [if_pos Ht]
    apply Nat.le_refl
  | inr Hf =>
    rw [if_neg Hf]
    cases (Nat.le_total l r) with
    | inl Hlr => exact absurd Hlr Hf
    | inr Hrl => exact Hrl
}

def Nat.max_r_le_split: (Nat.max l r ≤ m) = (l ≤ m ∧ r ≤ m) := by {
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

def Nat.max_l_le_split: (m ≤ Nat.max l r) = (m ≤ l ∨ m ≤ r) := by {
  apply propext;
  apply Iff.intro;
  case a.mp =>
    intro Hm
    let Hlr: r ≤ l ∨ l ≤ r := Nat.le_total r l;
    cases Hlr with
    | inl Hlr =>
      apply Or.inl;
      rw [<-(@Nat.max_val_l l r)]
      exact Hm
      exact Hlr
    | inr Hlr => 
      apply Or.inr;
      rw [<-(@Nat.max_val_r l r)]
      exact Hm
      exact Hlr
  case a.mpr =>
    intro Hm
    cases Hm with
    | inl Hm => exact Nat.le_trans Hm max_lt_l
    | inr Hm => exact Nat.le_trans Hm max_lt_r
}

def Nat.max_r_lt_split: (Nat.max l r < m) = (l < m ∧ r < m) := by {
  cases l with
  | zero => cases m with
    | zero => simp [Nat.not_lt_zero]
    | succ m => simp [Nat.zero_lt_succ]
  | succ l => cases r with
    | zero => sorry -- why not simp [Nat.zero_lt_succ]
    | succ r => sorry
}

def Nat.max_l_lt_split: (m < Nat.max l r) = (m < l ∨ m < r) := by {
  cases l with
  | zero => sorry
  | succ l => cases r with
    | zero => sorry
    | succ r => sorry
}

private def Nat.succ_right: n + Nat.succ l = Nat.succ (n + l) := rfl

def Nat.succ_le_succ_is_le: (succ n ≤ succ m) = (n ≤ m) :=
  propext (Iff.intro Nat.le_of_succ_le_succ Nat.succ_le_succ)

def Nat.succ_lt_succ_is_lt: (succ n < succ m) = (n < m) :=
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

def Nat.lt_is_succ_le: {n m: Nat} -> (n < m) = (Nat.succ n ≤ m) := rfl

def Nat.lt_l_add_lt: {n m l: Nat} -> n + m < l -> n < l := sorry

def Nat.lt_r_add_lt: {n m l: Nat} -> n + m < l -> m < l := sorry

def Nat.lt_sub_lt_add: {n m l: Nat} -> n + m < l -> n < l - m := sorry