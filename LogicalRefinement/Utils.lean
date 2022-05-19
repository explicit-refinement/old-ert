import Init.Data.Nat

def Nat.le_lt_succ (p: n ≤ m): (n < succ m) := Nat.lt_succ_of_le p

def Nat.le_or_lt (l r: Nat): l < r ∨ r ≤ l := by {
  cases Nat.le_total l r with
  | inl Hlr => 
    cases (Nat.decEq l r).em with
    | inl Heq => apply Or.inr; rw [Heq]; apply Nat.le_refl
    | inr Hne => exact Or.inl (Nat.lt_of_le_and_ne Hlr Hne)
  | inr Hrl => exact Or.inr Hrl
}

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

def Nat.max_le_l {l r: Nat}: l ≤ Nat.max l r := by {
  unfold Nat.max
  cases (Nat.decLe l r).em with
  | inl Ht =>
    rw [if_pos Ht]
    apply Ht
  | inr Hf =>
    rw [if_neg Hf]
    apply Nat.le_refl
}
 
def Nat.max_le_r {l r: Nat}: r ≤ Nat.max l r := by {
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
    exact ⟨Nat.le_trans max_le_l Hm, Nat.le_trans max_le_r Hm⟩
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
    | inl Hm => exact Nat.le_trans Hm max_le_l
    | inr Hm => exact Nat.le_trans Hm max_le_r
}

def Nat.max_r_lt_split: (Nat.max l r < m) = (l < m ∧ r < m) := by {
  apply propext;
  apply Iff.intro;
  case a.mp =>
    intro Hm
    apply And.intro
    case left =>
      exact Nat.lt_of_le_of_lt Nat.max_le_l Hm
    case right => 
      exact Nat.lt_of_le_of_lt Nat.max_le_r Hm
  case a.mpr =>
    intro ⟨Hl, Hr⟩
    cases Nat.le_total l r with
    | inl Hlr =>
      rw [Nat.max_val_r Hlr]
      exact Hr
    | inr Hlr =>
      rw [Nat.max_val_l Hlr]
      exact Hl
}

def Nat.max_l_lt_split: (m < Nat.max l r) = (m < l ∨ m < r) := by {
  apply propext;
  apply Iff.intro;
  case a.mp =>
    intro Hm
    cases Nat.le_total l r with
    | inl Hlr =>
      apply Or.inr
      rw [<-Nat.max_val_r Hlr]
      apply Hm
    | inr Hlr =>
      apply Or.inl
      rw [<-Nat.max_val_l Hlr]
      apply Hm
  case a.mpr =>
    intro Hm
    cases Hm with
    | inl Hl => exact Nat.le_trans Hl Nat.max_le_l
    | inr Hr => exact Nat.le_trans Hr Nat.max_le_r
}

private def Nat.succ_right: n + Nat.succ l = Nat.succ (n + l) := rfl

def Nat.succ_le_succ_is_le: (succ n ≤ succ m) = (n ≤ m) :=
  propext (Iff.intro Nat.le_of_succ_le_succ Nat.succ_le_succ)

def Nat.succ_lt_succ_is_lt: (succ n < succ m) = (n < m) :=
  propext (Iff.intro Nat.le_of_succ_le_succ Nat.succ_le_succ)

def Nat.zero_le_true: (0 ≤ n) = True :=
  propext (Iff.intro (λ _ => True.intro) (λ _ => Nat.zero_le _))

def Nat.le_sub_is_le_add: {l n m: Nat} -> (n - l ≤ m) = (n ≤ m + l) := by {
  intros l.
  induction l with
  | zero => intros; rfl
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

def Nat.le_antistep: succ n ≤ l -> n ≤ l := by {
  intro H;
  induction H with
  | refl => apply Nat.le_step; apply Nat.le_refl
  | @step m H I => apply Nat.le_step; apply I
}

def Nat.lt_antistep: succ n < l -> n < l := Nat.le_antistep

def Nat.lt_l_add_lt: {n m l: Nat} -> n + m < l -> n < l := by {
  intros n m;
  induction m with
  | zero => intros l H; exact H
  | succ m I => 
    intros l H;
    apply I
    apply Nat.lt_antistep
    rw [<-Nat.add_succ]
    apply H
}

def Nat.lt_r_add_lt: {n m l: Nat} -> n + m < l -> m < l := by {
  intros n m l;
  rw [Nat.add_comm]
  apply Nat.lt_l_add_lt
}

def Nat.lt_sub_lt_add: {l n m: Nat} -> n + m < l -> n < l - m := by {
  intros l;
  induction l with
  | zero => 
    intros n m H; 
    rw [Nat.zero_sub]
    apply Nat.lt_l_add_lt H
  | succ l Hl =>
    intros n m H;
    cases H with
    | refl =>
      let H': succ (n + m) = (succ n) + m := by {
        rw [Nat.add_comm]
        rw [<-Nat.add_succ]
        rw [Nat.add_comm]
      }
      rw [H']
      rw [Nat.add_sub_self_right]
      apply Nat.le_refl
    | step H =>
      apply Nat.le_trans _ (Nat.sub_le_succ_sub _ _)
      apply Hl
      apply H
}

theorem function_splitting {f g: A -> B}: f = g /\ x = y -> f x = g y := by {
  intro ⟨Hf, Hxy⟩;
  rw [Hf]
  rw [Hxy]
}

def Nat.succ_match_simp {F: Nat -> A}: (v: Nat) -> (
  match v + 1 with
  | 0 => e
  | Nat.succ n => F n 
) = F v := λv => rfl

theorem Nat.succ_sub_gt: {n m: Nat} -> m ≤ n -> n + 1 - m = (n - m) + 1 := by {
  intro n;
  induction n with
  | zero =>
    intro m
    rw [Nat.eq_zero_is_le_zero]
    intro H
    rw [H]
  | succ n I =>
    intro m H
    rw [Nat.add_succ, Nat.add_zero]
    cases m with
    | zero => simp
    | succ m =>
      repeat rw [Nat.succ_sub_succ_eq_sub]
      exact I (Nat.le_of_succ_le_succ H)
}

theorem Nat.add_sub_self_gt: {n m: Nat} -> m ≤ n -> n - m + m = n := by {
  intro n m;
  induction m with
  | zero => intros; rfl
  | succ m I =>
    intro H
    cases n with
    | zero => cases H
    | succ n =>
      rw [Nat.succ_le_succ_is_le] at H
      rw [succ_sub_succ_eq_sub]
      rw [add_succ]
      let R: succ (n - m + m) = n - m + 1 + m := by {
        rw [Nat.add_assoc]
        rw [@Nat.add_comm 1 m]
        rfl
      }
      rw [R]
      rw [<-Nat.succ_sub_gt H]
      exact I (Nat.le_succ_of_le H)
}

theorem or_imp_decompose {A B C D: Prop}: 
  (A -> C) ∧ (B -> D) -> A ∨ B -> C ∨ D 
  := by {
    intro ⟨F, G⟩;
    intro H;
    cases H with
    | inl H => exact Or.inl (F H)
    | inr H => exact Or.inr (G H)
  }

theorem and_imp_decompose {A B C: Prop}: (A ∧ B -> C) = (A -> B -> C) 
  := propext (Iff.intro (λF a b => F ⟨a, b⟩) (λF ⟨a, b⟩ => F a b))

theorem Nat.gt_sub_succ: n ≤ m -> (Nat.succ m) - n = Nat.succ (m - n) := by {
  revert n;
  induction m with
  | zero => intro n H; cases H; rfl
  | succ m I =>
    intro n;
    cases n with
    | zero => intro; simp
    | succ n =>
      intro H
      simp only [Nat.succ_sub_succ_eq_sub]
      exact I (Nat.le_of_succ_le_succ H)
}

theorem monorecursor
  : 
  @Eq.rec A x F D y p =
  @Eq.rec (Type) (F x rfl) (λA p => A) D (F y p) p'  
  := by {
    cases p;
    cases p';
    simp
  }

theorem rec_to_cast
  : 
  @Eq.rec A x F D y p =
  cast p' D 
  := by {
    cases p;
    cases p';
    simp [cast]
  }

theorem pair_mono_transport
  :
  @Eq.rec (Type) (Prod A B) (λA p => A) (x, y) (Prod C D) Ppair =
  (
    @Eq.rec (Type) A (λA p => A) x C PA, 
    @Eq.rec (Type) B (λA p => A) y D PB
  )
  := by {
    cases PA;
    cases PB;
    cases Ppair;
    rfl
  }

theorem rec_down
  {A: Type}
  {a: A}
  {M: (b: A) -> a = b -> Type}
  {D D': M a rfl}
  {b: A}
  {p p': a = b}
  (H: D = D'):
  @Eq.rec A a M D b p =
  @Eq.rec A a M D' b p'
  := by {
    cases H;
    rfl
  }