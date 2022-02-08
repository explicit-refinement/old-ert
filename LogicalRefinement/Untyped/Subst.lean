import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Untyped.Wk


def RawSubst := Nat -> RawUntyped

@[simp]
def RawSubst.id: RawSubst := RawUntyped.var

def RawSubst.wk1 (σ: RawSubst): RawSubst :=
  λv => RawUntyped.wk1 (σ v)

@[simp]
def RawWk.to_subst (σ: RawWk): RawSubst
  | v => RawUntyped.var (σ.var v)

def RawSubst.lift (σ: RawSubst): RawSubst
  | 0 => RawUntyped.var 0
  | Nat.succ n => wk1 σ n

@[simp]
def RawSubst.lift_succ (σ: RawSubst):
  lift σ (Nat.succ n) = wk1 σ n := rfl

@[simp]
def RawSubst.lift_zero (σ: RawSubst):
  lift σ 0 = RawUntyped.var 0 := rfl

@[simp]
def RawSubst.liftn: (l: Nat) -> (σ: RawSubst) -> RawSubst
  | 0, σ => σ
  | Nat.succ l, σ => lift (liftn l σ)

theorem RawSubst.liftn_lift_commute {σ: RawSubst}: 
  liftn n (lift σ) = lift (liftn n σ) := by {
  induction n with
  | zero => rfl
  | succ n I => simp [I] 
}

theorem RawSubst.liftn_commute {σ: RawSubst}: 
  liftn n (liftn m σ) = liftn m (liftn n σ) := by {
  induction n with
  | zero => rfl
  | succ n I =>
    simp only [liftn, RawSubst.liftn_lift_commute, I]
}

theorem RawSubst.lift_liftn_merge {n: Nat} {σ: RawSubst}:
  lift (liftn n σ) = liftn (n + 1) σ := rfl

theorem RawSubst.liftn_merge_outer: (m n: Nat) -> {σ: RawSubst} ->
  liftn n (liftn m σ) = liftn (n + m) σ := by {
  intro m;
  induction m with
  | zero => intros n σ; rfl
  | succ m I =>
    simp only [liftn, <-liftn_lift_commute]
    intros n σ;
    rw [I]
    rfl
}

theorem RawSubst.liftn_merge: (m n: Nat) -> {σ: RawSubst} ->
  liftn n (liftn m σ) = liftn (m + n) σ := by {
    simp only [liftn_merge_outer]
    intros m n σ;
    rw [Nat.add_comm]
}


theorem RawSubst.liftn_base_nil: (base: Nat) -> (σ: RawSubst) -> 
  (v: Nat) -> v < base ->
  liftn base σ v = RawUntyped.var v := by {
  intros base;
  induction base with
  | zero =>
    intros σ v H;
    cases H
  | succ base I =>
    intros σ v H;
    simp only [liftn];
    cases v with
    | zero => rfl
    | succ v => 
      simp only [lift, wk1]
      rw [I]
      simp
      rw [<-Nat.succ_lt_succ_is_lt]
      apply H
}

theorem RawSubst.liftn_above_wk: (base: Nat) -> (σ: RawSubst) -> 
  (v: Nat) -> base ≤ v ->
  liftn base σ v = RawUntyped.wkn base (σ (v - base)) := by {
    intros base;
    induction base with
    | zero => simp
    | succ base I =>
      intros σ v H;
      simp only [liftn, RawUntyped.wkn, RawWk.wkn]
      cases v with
      | zero => cases H
      | succ v => 
        simp only [lift, wk1, RawUntyped.wk1]
        rw [Nat.succ_sub_succ_eq_sub]
        rw [<-RawWk.step_is_comp_wk1]
        rw [<-RawUntyped.wk_composes]
        rw [I]
        simp
        apply Nat.le_of_succ_le_succ
        apply H
}

@[simp]
def RawUntyped.subst (σ: RawSubst): RawUntyped -> RawUntyped
  | var v => σ v
  | const c => const c
  | unary k t => unary k (subst σ t)
  | let_bin k t => let_bin k (subst (RawSubst.liftn 2 σ) t)
  | bin k l r => bin k (subst σ l) (subst σ r)
  | abs k A t => abs k (subst σ A) (subst (RawSubst.lift σ) t)
  | cases k d l r => cases k (subst σ d) (subst σ l) (subst σ r)

theorem RawSubst.lift_var: {n v: Nat} -> {σ: RawSubst} -> 
  (liftn (n + 1) σ) (RawWk.var (RawWk.wknth n) v) 
  = RawUntyped.wknth n (liftn n σ v) 
  := by {
    intros n v σ;
    cases Nat.le_or_lt v n with
    | inl Hnv =>
      rw [liftn_base_nil _ _ _ Hnv]
      rw [liftn_base_nil]
      simp only [RawUntyped.wknth, RawUntyped.wk]
      rw [RawWk.wknth_small Hnv]
      exact Nat.le_step Hnv
    | inr Hnv =>
      rw [liftn_above_wk _ _ _ Hnv]
      rw [liftn_above_wk]
      simp only [
        RawUntyped.wknth, RawUntyped.wk, RawUntyped.wkn, RawWk.wkn, Nat.add]
      rw [RawWk.wknth_big Hnv]
      rw [Nat.succ_sub_succ_eq_sub]
      rw [RawUntyped.wk_composes]
      rw [RawUntyped.wk_coherent RawWk.wknth_wkn_equiv]
      simp
      rw [RawWk.wknth_big Hnv]
      exact Nat.succ_le_succ Hnv
  }

theorem RawUntyped.liftn_wk {u: RawUntyped}: {σ: RawSubst} -> (n: Nat) ->
  subst (RawSubst.liftn (n + 1) σ) (wknth n u) =
  wknth n (subst (RawSubst.liftn n σ) u)
  := by {
    unfold RawWk.wk1
    induction u with
    | var v =>
      intros σ n;
      simp only [subst]
      rw [RawSubst.lift_var]
    | const c => simp
    | unary k t I => 
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at I
      rw [I]
    | let_bin k e I =>
      intros σ n
      simp only [wknth, wk, subst, RawWk.liftn_wknth_merge]
      rw [RawSubst.liftn_merge]
      simp only [wknth] at I
      rw [I]
      simp
    | bin k l r Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at Il
      simp only [wknth] at Ir
      rw [Il]
      rw [Ir]
    | abs k A t IA It => 
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at IA
      simp only [wknth] at It
      rw [IA]
      rw [RawWk.lift_wknth_merge]
      rw [RawSubst.lift_liftn_merge]
      rw [RawSubst.lift_liftn_merge]
      rw [It]
      exact 0 -- TODO: why?
    | cases k d l r Id Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at Id
      simp only [wknth] at Il
      simp only [wknth] at Ir
      rw [Id]
      rw [Il]
      rw [Ir]
  }

theorem RawSubst.lift_wk {u: RawUntyped}: {σ: RawSubst} ->
  RawUntyped.subst (lift σ) (RawUntyped.wk1 u) 
  = RawUntyped.wk1 (RawUntyped.subst σ u) := by {
    intros σ;
    apply RawUntyped.liftn_wk 0
}

def RawSubst.comp (σ ρ: RawSubst): RawSubst
  | v => RawUntyped.subst σ (ρ v)

@[simp] theorem RawSubst.lift_comp {ρ σ: RawSubst}: 
  comp (lift ρ) (lift σ) = lift (comp ρ σ) := by {
    funext v;
    cases v with
    | zero => simp [comp]
    | succ v => simp only [lift_succ, comp, wk1, lift_wk]
  }

@[simp]
def RawUntyped.subst_composes (u: RawUntyped):
  (σ ρ: RawSubst) -> subst σ (subst ρ u) = subst (RawSubst.comp σ ρ) u
  := by {
  induction u with
  | var v => simp [RawSubst.comp]
  | const c => simp
  | unary k t I => simp [I]
  | let_bin k t I => simp [I]
  | bin k l r Il Ir => simp [Il, Ir]
  | abs k A t IA It => simp [IA, It]
  | cases k d l r Id Il Ir => simp [Id, Il, Ir]
}

@[simp] theorem RawSubst.comp_assoc {ρ σ τ: RawSubst}:
  comp ρ (comp σ τ) = comp (comp ρ σ) τ := by {
    funext v;
    simp [comp]
  }