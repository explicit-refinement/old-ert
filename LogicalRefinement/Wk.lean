inductive Wk: Type 0 where
  | id: Wk
  | step: Wk -> Wk
  | lift: Wk -> Wk

@[simp] def Wk.wk1: Wk := step id

@[simp] def Wk.liftn: Wk -> Nat -> Wk
  | ρ, 0 => ρ
  | ρ, Nat.succ n => Wk.lift (ρ.liftn n)

@[simp] def Wk.wkn: Nat -> Wk
  | 0 => id
  | Nat.succ n => step (wkn n)

@[simp] def Wk.wknth (n: Nat): Wk := wk1.liftn n

@[simp]
theorem Wk.lift_liftn_merge {ρ: Wk} {m n: Nat}: 
  (ρ.liftn n).lift = ρ.liftn (n + 1) := rfl

@[simp]
theorem Wk.liftn_merge {ρ: Wk}: {n m: Nat} -> 
  (ρ.liftn m).liftn n = ρ.liftn (n + m) := by {
    intro n;
    induction n with
    | zero => simp
    | succ n I =>
      intros m;
      rw [Nat.add_comm]
      rw [Nat.add_succ]
      rw [Nat.add_comm]
      simp [I]
  }

@[simp]
theorem Wk.lift_wknth_merge {m n: Nat}: lift (wknth n) = wknth (n + 1) 
  := by {
  unfold wknth;
  apply lift_liftn_merge;
  exact 0
}

@[simp]
theorem Wk.liftn_wknth_merge {m n: Nat}: (wknth n).liftn m = wknth (n + m) 
  := by {
  unfold wknth;
  rw [liftn_merge]
  rw [Nat.add_comm]
}

@[simp] 
def Wk.comp: Wk -> Wk -> Wk
    | Wk.id, σ => σ
    | Wk.step ρ, σ => Wk.step (comp ρ σ)
    | Wk.lift ρ, Wk.id => Wk.lift ρ
    | Wk.lift ρ, Wk.step σ => Wk.step (comp ρ σ)
    | Wk.lift ρ, Wk.lift σ => Wk.lift (comp ρ σ)

@[simp] 
theorem Wk.comp_id_left_id {ρ: Wk}: Wk.comp Wk.id ρ = ρ := rfl

@[simp] 
theorem Wk.comp_id_right_id: {ρ: Wk} -> Wk.comp ρ Wk.id = ρ
  | Wk.id => rfl
  | Wk.lift ρ => rfl
  | Wk.step ρ => by {
    simp
    exact comp_id_right_id
  }

def Wk.step_is_comp_wk1: comp wk1 ρ = step ρ := rfl

@[simp] 
theorem Wk.comp_assoc: {ρ σ τ: Wk} -> 
  Wk.comp (Wk.comp ρ σ) τ = Wk.comp ρ (Wk.comp σ τ) := by {
    intro ρ;
    induction ρ <;> 
    intro σ <;> 
    induction σ <;>
    intro τ <;>
    induction τ <;>
    simp [*]
  }

@[simp] 
theorem Wk.lift_comp {ρ σ: Wk}: 
  Wk.comp (Wk.lift ρ) (Wk.lift σ) = Wk.lift (Wk.comp ρ σ) := rfl

@[simp] 
def Wk.var: Wk -> Nat -> Nat
  | Wk.id, n => n
  | Wk.step ρ, n => (var ρ n) + 1
  | Wk.lift ρ, 0 => 0
  | Wk.lift ρ, (n + 1) => (var ρ n) + 1

def Wk.equiv (ρ σ: Wk) := ∀v: Nat, var ρ v = var σ v

def Wk.equiv_refl {ρ: Wk}: equiv ρ ρ := λ_ => rfl

def Wk.equiv_sym {ρ σ: Wk}: equiv ρ σ = equiv σ ρ := by {
  simp only [equiv];
  apply propext;
  apply Iff.intro;
  case a.mp => 
    intros H v
    simp [H]
  case a.mpr =>
    intros H v
    simp [H]
}

def Wk.equiv_trans {ρ σ τ: Wk}: 
  equiv ρ σ -> equiv σ τ -> equiv ρ τ := by {
    intros Hρσ Hστ v;
    rw [Hρσ]
    rw [Hστ]
  }

def Wk.wk1_lift_eqiv {ρ: Wk}:
  equiv (Wk.comp (lift ρ) wk1) (Wk.comp wk1 ρ)  := by {
    simp
    apply equiv_refl
  }

def Wk.lift_equiv {ρ σ: Wk}:
  equiv ρ σ -> equiv (lift ρ) (lift σ) := by {
    intros H v;
    cases v with
    | zero => simp
    | succ v => simp only [var]; rw [H]
  }

def Wk.liftn_equiv: {n: Nat} -> {ρ σ: Wk} ->
  equiv ρ σ -> equiv (ρ.liftn n) (σ.liftn n) := by {
    intro n;
    induction n with
    | zero => intros ρ σ H; exact H
    | succ n I => 
      intros ρ σ H;
      simp only [liftn]
      apply Wk.lift_equiv
      apply I
      exact H
  }

def Wk.lift_id_equiv: equiv (lift id) id := by {
    intros v;
    cases v with
    | zero => rfl
    | succ v => rfl
  }

def Wk.liftn_id_equiv: {n: Nat} -> equiv (id.liftn n) id := by {
    intro n;
    induction n with
    | zero => exact equiv_refl
    | succ n I => 
      simp only [liftn];
      intros v;
      cases v with
      | zero => rfl
      | succ v =>
        simp only [var]
        rw [I]
        rfl
  }

@[simp] def Wk.wk1_var: var wk1 n = n + 1 := rfl  

@[simp] def Wk.wk1_step: step ρ = wk1.comp ρ := rfl

@[simp] def Wk.wkn_succ_0_var: var (wknth (Nat.succ n)) 0 = 0 := rfl

@[simp] def Wk.wkn_succ_succ_var: 
  var (wknth (Nat.succ n)) (Nat.succ m) = Nat.succ (var (wknth n) m) := by {
    rw[<-lift_wknth_merge]
    simp only [var]
    exact 0
}

@[simp] def Wk.wkn_var:
  var (wkn n) v = v + n := by {
  induction n with
  | zero => rfl
  | succ n I =>
    simp only [wkn, var]
    rw [I]
    rfl
}

def Wk.wknth_small: {n v: Nat} -> v < n -> var (wknth n) v = v := by {
  intros n;
  induction n with
  | zero => intro v H; cases H
  | succ n I => 
    intro v H;
    simp only [wknth, liftn]
    cases v with
    | zero => rfl
    | succ v => 
      simp only [var]
      simp only [wknth] at I
      rw [I]
      exact Nat.le_of_succ_le_succ H
}

def Wk.wknth_big: {n v: Nat} -> n ≤ v -> var (wknth n) v = v + 1 := by {
  intros n;
  induction n with
  | zero => simp
  | succ n I => 
    intro v H;
    simp only [wknth, liftn]
    cases v with
    | zero => cases H
    | succ v => 
      simp only [var]
      simp only [wknth] at I
      rw [I]
      exact Nat.le_of_succ_le_succ H
}

def Wk.wknth_wkn_equiv: equiv (comp (wknth n) (wkn n)) (wkn (n + 1)) := by {
  induction n with
  | zero =>
    exact equiv_refl
  | succ n I =>
    intro v;
    simp only [var]
    simp only [wknth] at I
    rw [I v]
    simp
}

@[simp] 
theorem Wk.var_comp: (ρ σ: Wk) -> (n: Nat) ->
  Wk.var ρ (Wk.var σ n) = Wk.var (Wk.comp ρ σ) n
  | Wk.id, _, _ => rfl
  | _, Wk.id, _ => by { simp }
  | Wk.step ρ, _, _ => by { simp; apply var_comp }
  | Wk.lift ρ, Wk.step σ, _ => by { simp; apply var_comp }
  | Wk.lift ρ, Wk.lift σ, 0 => by { simp } 
  | Wk.lift ρ, Wk.lift σ, (n + 1) => by { simp; apply var_comp }  
 
def Wk.maps (ρ: Wk) (m n: Nat): Prop := (l: Nat) -> l < n -> Wk.var ρ l < m

theorem Wk.id_maps {n: Nat}: Wk.id.maps n n  := λ_ => λH => H

theorem Wk.step_maps {ρ: Wk} {m n: Nat} : ρ.maps m n -> ρ.step.maps (m + 1) n := by {
  intros Hρ l Hl;
  simp;
  apply Nat.succ_lt_succ;
  apply Hρ;
  apply Hl
}

theorem Wk.lift_maps {ρ: Wk} {m n: Nat}: 
  ρ.maps m n -> ρ.lift.maps (m + 1) (n + 1) := by {
  intros Hρ l Hl;
  cases l with
  | zero => simp; apply Nat.zero_lt_succ
  | succ => 
    simp
    apply Nat.succ_lt_succ
    apply Hρ
    apply Nat.lt_of_succ_lt_succ
    apply Hl
}

theorem Wk.wk1_maps {n: Nat}: wk1.maps (n + 1) n
  := λ v Hv => Nat.succ_le_succ Hv

theorem Wk.liftn_maps {ρ: Wk} {l m n: Nat}: 
  ρ.maps m n -> (ρ.liftn l).maps (m + l) (n + l) := by {
  induction l with
  | zero => intros Hρ. apply Hρ
  | succ l I => 
    intros Hρ;
    apply lift_maps
    apply I
    apply Hρ
}

theorem Wk.comp_maps {ρ σ: Wk} {m n l: Nat}:
  ρ.maps m n -> σ.maps n l -> (ρ.comp σ).maps m l := by {
  intros Hρ Hσ l Hl;
  rw[←var_comp];
  apply Hρ;
  apply Hσ;
  apply Hl
}