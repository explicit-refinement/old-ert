import LogicalRefinement.Wk

def Sparsity := List Bool

@[simp]
def Sparsity.dep: Sparsity -> Nat -> Bool
| [], n => true
| b::Hs, 0 => b
| b::Hs, Nat.succ n => dep Hs n

theorem Sparsity.dep_get? {Γ: Sparsity} {n b}
  : Γ.get? n = some b -> Γ.dep n = b
  := by {
    revert n;
    induction Γ with
    | nil => intro n H; cases H
    | cons H Γ I =>
      intro n Hn;
      cases n with
      | zero => simp [List.get?] at Hn; simp [Hn]
      | succ n => simp only [dep, I Hn]
  }

def Sparsity.wknth: Sparsity -> Nat -> Bool -> Sparsity
| H::Γ, Nat.succ n, b => H::(wknth Γ n b)
| [], Nat.succ n, b => true::(wknth [] n b)
| Γ, 0, b => b::Γ

def Sparsity.wk1_char {b: Bool} (Γ: Sparsity)
  : Γ.wknth 0 b = (b::Γ)
  := by simp only [wknth]

@[simp]
def Sparsity.ix: Sparsity -> Nat -> Nat
| true::Hs, Nat.succ n => (ix Hs n) + 1
| false::Hs, Nat.succ n => ix Hs n
| _, n => n

@[simp]
def Sparsity.ix_inv: Sparsity -> Nat -> Nat
| true::Hs, Nat.succ n => (ix_inv Hs n) + 1
| false::Hs, n => (ix_inv Hs n) + 1
| _, n => n

@[simp]
theorem Sparsity.ix_zero (Γ: Sparsity)
  : Γ.ix 0 = 0
  := by cases Γ with
        | nil => rfl
        | cons H T => cases H <;> rfl

theorem Sparsity.ix_monotonic (Γ: Sparsity)
  : ∀{n m}, n ≤ m -> Γ.ix n ≤ Γ.ix m
  := by {
    induction Γ with
    | nil => intros; simp; assumption
    | cons H Γ I =>
      intro n m Hnm
      cases m with
      | zero => 
        cases Hnm
        apply Nat.le_refl
      | succ m =>
        cases n with
        | zero => rw [ix_zero]; apply Nat.zero_le
        | succ n =>
          have I' := I (Nat.le_of_succ_le_succ Hnm);
          cases H with
          | true => exact Nat.succ_le_succ I'
          | false => exact I'
  }

theorem Sparsity.ix_inv_valid (Γ: Sparsity) {n: Nat}:
  Γ.dep n = true -> Γ.ix_inv (Γ.ix n) = n
  := by {
    revert n;
    induction Γ with
    | nil => intro n H; rfl
    | cons H Γ I =>
      intro n;
      cases n with
      | zero => 
        intro Hn;
        cases H with
        | true => rfl
        | false => simp [List.get?] at Hn
      | succ n =>
        intro Hn;
        cases H <;> simp [ix, ix_inv, I Hn] 
  }

theorem Sparsity.ix_inv_subvalid (Γ: Sparsity) {n: Nat}
  : n ≤ Γ.ix_inv (Γ.ix n)
  := by {
    revert n;
    induction Γ with
    | nil => simp
    | cons H Γ I => 
      intro n;
      cases n with
      | zero => cases H <;> simp
      | succ n => cases H <;> exact Nat.succ_le_succ I
  }

theorem Sparsity.ix_inv_monotonic (Γ: Sparsity) {n m: Nat}
  : n ≤ m -> Γ.ix_inv n ≤ Γ.ix_inv m
  := by {
    revert n m;
    induction Γ with
    | nil => intros; assumption
    | cons H Γ I =>
      intro n m Hnm;
      cases n with
      | zero =>
        cases m with
        | zero => simp
        | succ m => cases H with
                    | true => apply Nat.zero_le
                    | false =>
                      apply Nat.succ_le_succ
                      apply I
                      apply Nat.zero_le
      | succ n => 
        cases m with
        | zero => cases Hnm
        | succ m => 
          cases H with
          | true =>
            exact Nat.succ_le_succ (I (Nat.le_of_succ_le_succ Hnm))
          | false =>
            exact Nat.succ_le_succ (I Hnm)
  }

def Sparsity.wknth_dep {Γ: Sparsity} {n b v}
  : (Γ.wknth n b).dep ((Wk.wknth n).var v) = Γ.dep v
  := by {
    rw [Wk.wknth_var]
    revert b v Γ;
    induction n with
    | zero => 
      intro Γ b v;
      rw [Sparsity.wk1_char]
      rfl
    | succ n I =>
      intro Γ b v;
      cases v with
      | zero => cases Γ <;> rfl
      | succ v => cases Γ <;> simp [I]
  }
  
def Sparsity.wknth_ix_false {Γ: Sparsity} {n v}
: (Γ.wknth n false).ix ((Wk.wknth n).var v) = Γ.ix v
:= by {
  rw [Wk.wknth_var]
  revert v Γ;
  induction n with
  | zero => 
    intro Γ v;
    rw [Sparsity.wk1_char]
    rfl
  | succ n I =>
    intro Γ v;
    cases v with
    | zero =>
      cases Γ with
      | nil => rfl
      | cons H Γ => cases H <;> rfl
    | succ v =>
      cases Γ with
      | nil => simp [I]
      -- Lean really needs to learn how to ignore arguments...
      | cons H Γ => cases H <;> simp [I]
}

def Sparsity.wknth_ix_true' {Γ: Sparsity} {n v}
: (Γ.wknth n true).ix ((Wk.wknth n).var v) 
= if v < n then Γ.ix v else (Γ.ix v) + 1
:= by {
  rw [Wk.wknth_var]
  revert v Γ;
  --TODO: shorten...
  induction n with
  | zero => 
    intro Γ v;
    rw [Sparsity.wk1_char]
    rfl
  | succ n I =>
    intro Γ v;
    cases v with
    | zero =>
      split
      . cases Γ with
        | nil => rfl
        | cons H Γ => 
          simp only [wknth]
          rw [ix_zero]
          simp only [wknth_var, ix_zero]
      . have _: 0 < Nat.succ n := n.zero_lt_succ;
        contradiction
    | succ v =>
      cases Γ with
      | nil => 
        simp only [wknth_var, ix, I]
        split <;> split
        . rfl
        . have _: Nat.succ v < Nat.succ n := 
            by apply Nat.succ_lt_succ; assumption;
          contradiction
        . have _: v < n := 
            by apply Nat.lt_of_succ_lt_succ; assumption;
          contradiction
        . rfl
      | cons H Γ => 
        simp only [wknth_var]
        cases H with
        | true => 
          simp only [ix, I]
          split <;> split
          . rfl
          . have _: Nat.succ v < Nat.succ n := 
              by apply Nat.succ_lt_succ; assumption;
            contradiction
          . have _: v < n := 
              by apply Nat.lt_of_succ_lt_succ; assumption;
            contradiction
          . rfl
        | false => 
          simp only [ix, I]
          split <;> split
          . rfl
          . have _: Nat.succ v < Nat.succ n := 
              by apply Nat.succ_lt_succ; assumption;
            contradiction
          . have _: v < n := 
              by apply Nat.lt_of_succ_lt_succ; assumption;
            contradiction
          . rfl
}

def Sparsity.wknth_merge {Γ: Sparsity} {n b H}
  : H::(Γ.wknth n b) = wknth (H::Γ) (Nat.succ n) b
  := rfl

inductive WkSprs: Wk -> Sparsity -> Sparsity -> Prop
  | id: WkSprs Wk.id Γ Γ
  | step: WkSprs ρ Γ Δ -> WkSprs (Wk.step ρ) (b::Γ) Δ
  | lift: WkSprs ρ Γ Δ -> WkSprs (Wk.lift ρ) (b::Γ) (b::Δ)

theorem WkSprs.trans_dep
  : WkSprs ρ Γ Δ -> Γ.dep (ρ.var v) = Δ.dep v
  := by {
    intro H;
    revert v;
    induction H with
    | id => intro; rfl
    | step H I =>
      intro
      rw [<-I]
      rfl
    | lift H I =>
      intro v;
      cases v with
      | zero => rfl
      | succ v => exact I
  }