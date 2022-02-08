inductive RawWk: Type 0 where
  | id: RawWk
  | step: RawWk -> RawWk
  | lift: RawWk -> RawWk

@[simp] def RawWk.wk1: RawWk := step id

@[simp] def RawWk.liftn: (l: Nat) -> RawWk -> RawWk
  | 0, ρ => ρ
  | Nat.succ n, ρ => RawWk.lift (liftn n ρ)

@[simp] def RawWk.wkn: Nat -> RawWk
  | 0 => id
  | Nat.succ n => step (wkn n)

@[simp] def RawWk.wknth (n: Nat): RawWk := liftn n wk1

@[simp]
theorem RawWk.lift_liftn_merge {m n: Nat}: 
  lift (liftn n σ) = liftn (n + 1) σ := rfl

@[simp]
theorem RawWk.liftn_merge: {n m: Nat} -> 
  liftn n (liftn m σ) = liftn (n + m) σ := by {
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
theorem RawWk.lift_wknth_merge {m n: Nat}: lift (wknth n) = wknth (n + 1) 
  := by {
  unfold wknth;
  apply lift_liftn_merge;
  exact 0
}

@[simp]
theorem RawWk.liftn_wknth_merge {m n: Nat}: liftn m (wknth n) = wknth (n + m) 
  := by {
  unfold wknth;
  rw [liftn_merge]
  rw [Nat.add_comm]
}

@[simp] def RawWk.comp: RawWk -> RawWk -> RawWk
    | RawWk.id, σ => σ
    | RawWk.step ρ, σ => RawWk.step (comp ρ σ)
    | RawWk.lift ρ, RawWk.id => RawWk.lift ρ
    | RawWk.lift ρ, RawWk.step σ => RawWk.step (comp ρ σ)
    | RawWk.lift ρ, RawWk.lift σ => RawWk.lift (comp ρ σ)

theorem raw_wk_comp_id_left_id {ρ: RawWk}: RawWk.comp RawWk.id ρ = ρ := rfl

def RawWk.step_is_comp_wk1: comp wk1 ρ = step ρ := rfl

@[simp] theorem raw_wk_comp_id_right_id: {ρ: RawWk} -> RawWk.comp ρ RawWk.id = ρ
  | RawWk.id => rfl
  | RawWk.lift ρ => rfl
  | RawWk.step ρ => by {
    simp
    apply raw_wk_comp_id_right_id
  }

@[simp] theorem raw_wk_comp_assoc: {ρ σ τ: RawWk} -> 
  RawWk.comp (RawWk.comp ρ σ) τ = RawWk.comp ρ (RawWk.comp σ τ)
  | RawWk.id, _, _ => rfl
  | _, RawWk.id, _ => by {
    simp
  }
  | _, _, RawWk.id => by simp
  | RawWk.step ρ, _, _ => by {
    simp
    apply raw_wk_comp_assoc
  }
  | RawWk.lift ρ, RawWk.step σ, _ => by {
    simp
    apply raw_wk_comp_assoc
  }
  | RawWk.lift ρ, RawWk.lift σ, RawWk.step τ => by {
    simp
    apply raw_wk_comp_assoc
  }
  | RawWk.lift ρ, RawWk.lift σ, RawWk.lift τ => by {
    simp
    apply raw_wk_comp_assoc
  }

@[simp] theorem raw_wk_lift_comp {ρ σ: RawWk}: 
  RawWk.comp (RawWk.lift ρ) (RawWk.lift σ) = RawWk.lift (RawWk.comp ρ σ) := rfl

@[simp] def RawWk.var: RawWk -> Nat -> Nat
  | RawWk.id, n => n
  | RawWk.step ρ, n => (var ρ n) + 1
  | RawWk.lift ρ, 0 => 0
  | RawWk.lift ρ, (n + 1) => (var ρ n) + 1

def RawWk.equiv (ρ σ: RawWk) := ∀v: Nat, var ρ v = var σ v

def RawWk.equiv_refl {ρ: RawWk}: equiv ρ ρ := λ_ => rfl

def RawWk.equiv_sym {ρ σ: RawWk}: equiv ρ σ = equiv σ ρ := by {
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

def RawWk.equiv_trans {ρ σ τ: RawWk}: 
  equiv ρ σ -> equiv σ τ -> equiv ρ τ := by {
    intros Hρσ Hστ v;
    rw [Hρσ]
    rw [Hστ]
  }

def RawWk.lift_equiv {ρ σ: RawWk}:
  equiv ρ σ -> equiv (lift ρ) (lift σ) := by {
    intros H v;
    cases v with
    | zero => simp
    | succ v => simp only [var]; rw [H]
  }

def RawWk.liftn_equiv: {n: Nat} -> {ρ σ: RawWk} ->
  equiv ρ σ -> equiv (liftn n ρ) (liftn n σ) := by {
    intro n;
    induction n with
    | zero => intros ρ σ H; exact H
    | succ n I => 
      intros ρ σ H;
      simp only [liftn]
      apply RawWk.lift_equiv
      apply I
      exact H
  }

def RawWk.lift_id_equiv: equiv (lift id) id := by {
    intros v;
    cases v with
    | zero => rfl
    | succ v => rfl
  }

def RawWk.liftn_id_equiv: {n: Nat} -> equiv (liftn n id) id := by {
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

@[simp] def RawWk.wk1_var: var wk1 n = n + 1 := rfl  

@[simp] def RawWk.wkn_succ_0_var: var (wknth (Nat.succ n)) 0 = 0 := rfl

@[simp] def RawWk.wkn_succ_succ_var: 
  var (wknth (Nat.succ n)) (Nat.succ m) = Nat.succ (var (wknth n) m) := by {
    rw[<-lift_wknth_merge]
    simp only [var]
    exact 0
}

def RawWk.wknth_small: {n v: Nat} -> v < n -> var (wknth n) v = v := by {
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

def RawWk.wknth_big: {n v: Nat} -> n ≤ v -> var (wknth n) v = v + 1 := by {
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

def RawWk.wknth_wkn_equiv: equiv (comp (wknth n) (wkn n)) (wkn (n + 1)) := by {
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

@[simp] theorem raw_wk_var_comp: (ρ σ: RawWk) -> (n: Nat) ->
  RawWk.var ρ (RawWk.var σ n) = RawWk.var (RawWk.comp ρ σ) n
  | RawWk.id, _, _ => rfl
  | _, RawWk.id, _ => by { simp }
  | RawWk.step ρ, _, _ => by { simp; apply raw_wk_var_comp }
  | RawWk.lift ρ, RawWk.step σ, _ => by { simp; apply raw_wk_var_comp }
  | RawWk.lift ρ, RawWk.lift σ, 0 => by { simp } 
  | RawWk.lift ρ, RawWk.lift σ, (n + 1) => by { simp; apply raw_wk_var_comp }  

@[simp] def wk_maps (m n: Nat) (ρ: RawWk): Prop := (l: Nat) -> l < n -> RawWk.var ρ l < m

theorem wk_maps_id {n: Nat}: wk_maps n n RawWk.id := λ_ => λH => H

theorem wk_maps_step {m n: Nat} {ρ: RawWk}: wk_maps m n ρ -> wk_maps (m + 1) n (RawWk.step ρ) := by {
  intros Hρ l Hl;
  simp;
  apply Nat.succ_lt_succ;
  apply Hρ;
  apply Hl
}

theorem wk_maps_lift {m n: Nat} {ρ: RawWk}: 
  wk_maps m n ρ -> wk_maps (m + 1) (n + 1) (RawWk.lift ρ) := by {
  intros Hρ l Hl;
  cases l with
  | zero => simp; apply Nat.zero_lt_succ
  | succ => 
    simp; 
    apply Nat.succ_lt_succ; 
    apply Hρ; 
    apply Nat.lt_of_succ_lt_succ; 
    apply Hl
}

theorem wk_maps_wk1 {n: Nat}: wk_maps (n + 1) n RawWk.wk1 
  := λ v Hv => Nat.succ_le_succ Hv

theorem wk_maps_liftn {l m n: Nat} {ρ: RawWk}: 
  wk_maps m n ρ -> wk_maps (m + l) (n + l) (RawWk.liftn l ρ) := by {
  induction l with
  | zero => intros Hρ. apply Hρ
  | succ l I => 
    intros Hρ.
    (apply wk_maps_lift).
    (apply I).
    apply Hρ
}

theorem wk_maps_comp {m n l: Nat} {ρ σ: RawWk}:
  wk_maps m n ρ -> wk_maps n l σ -> wk_maps m l (RawWk.comp ρ σ) := by {
  intros Hρ Hσ l Hl;
  rw[←raw_wk_var_comp];
  apply Hρ;
  apply Hσ;
  apply Hl
}

structure Wk (m n: Nat) := (val: RawWk) (p: wk_maps m n val)

@[simp] def Wk.id {n: Nat}: Wk n n := Wk.mk RawWk.id (@wk_maps_id n)

@[simp] def Wk.step {m n: Nat} (ρ: Wk m n): Wk (m + 1) n := 
  Wk.mk (RawWk.step ρ.val) (wk_maps_step ρ.p)

@[simp] def Wk.lift {m n: Nat} (ρ: Wk m n): Wk (m + 1) (n + 1) := 
  Wk.mk (RawWk.lift ρ.val) (wk_maps_lift ρ.p)
  
@[simp] def Wk.liftn: (l: Nat) -> Wk m n -> Wk (m + l) (n + l)
  | 0, ρ => ρ
  | Nat.succ n, ρ => Wk.lift (liftn n ρ)

@[simp] def Wk.comp (ρ: Wk m n) (σ: Wk n l): Wk m l :=
  Wk.mk (RawWk.comp ρ.val σ.val) (wk_maps_comp ρ.p σ.p)

@[simp] theorem wk_comp_assoc (ρ: Wk m n) (σ: Wk n l) (τ: Wk l p):
  Wk.comp ρ (Wk.comp σ τ) = Wk.comp (Wk.comp ρ σ) τ := by {
  simp
}

@[simp] def Wk.raw_var (ρ: Wk m n): Nat -> Nat := RawWk.var ρ.val

@[simp] def Wk.var (ρ: Wk m n): Fin n -> Fin m
  | Fin.mk v p => Fin.mk (Wk.raw_var ρ v) (ρ.p v p)

@[simp] theorem wk_var_comp (ρ: Wk m n) (σ: Wk n l) (v: Fin l):
  Wk.var ρ (Wk.var σ v) = Wk.var (Wk.comp ρ σ) v := by {
  simp
}

@[simp] theorem wk_lift_comp {ρ: Wk m n} {σ: Wk n l}: 
  Wk.comp (Wk.lift ρ) (Wk.lift σ) = Wk.lift (Wk.comp ρ σ) := rfl

def Wk.wk1: Wk (n + 1) n := Wk.step Wk.id