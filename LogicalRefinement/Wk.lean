inductive RawWk: Type 0 where
  | id: RawWk
  | step: RawWk -> RawWk
  | lift: RawWk -> RawWk

@[simp] def RawWk.comp: RawWk -> RawWk -> RawWk
    | RawWk.id, σ => σ
    | RawWk.step ρ, σ => RawWk.step (comp ρ σ)
    | RawWk.lift ρ, RawWk.id => RawWk.lift ρ
    | RawWk.lift ρ, RawWk.step σ => RawWk.step (comp ρ σ)
    | RawWk.lift ρ, RawWk.lift σ => RawWk.lift (comp ρ σ)

theorem raw_wk_comp_id_left_id {ρ: RawWk}: RawWk.comp RawWk.id ρ = ρ := rfl

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
  | succ => simp; apply Nat.succ_lt_succ; apply Hρ; apply Nat.lt_of_succ_lt_succ; apply Hl
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