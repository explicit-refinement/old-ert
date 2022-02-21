import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Untyped.Wk

def Subst := Nat -> Untyped

@[simp]
def Subst.id: Subst := Untyped.var

def Subst.wk1 (σ: Subst): Subst :=
  λv => Untyped.wk1 (σ v)

@[simp]
def Wk.to_subst (σ: Wk): Subst
  | v => Untyped.var (σ.var v)

def Subst.lift (σ: Subst): Subst
  | 0 => Untyped.var 0
  | Nat.succ n => wk1 σ n

def Wk.to_subst_lift {σ: Wk}: 
  (to_subst σ).lift = to_subst σ.lift := by {
  funext v;
  cases v with
  | zero => simp [Subst.lift]
  | succ n => simp [Subst.lift, Subst.wk1]
}

@[simp]
def Subst.lift_succ (σ: Subst):
  σ.lift (Nat.succ n) = wk1 σ n := rfl

@[simp]
def Subst.lift_zero (σ: Subst):
  σ.lift 0 = Untyped.var 0 := rfl

@[simp]
def Subst.liftn: (σ: Subst) -> (l: Nat) -> Subst
  | σ, 0 => σ
  | σ, Nat.succ l => (σ.liftn l).lift

def Wk.to_subst_liftn: {n: Nat} -> {σ: Wk} ->
  (to_subst σ).liftn n = to_subst (σ.liftn n) := by {
    intro n;
    induction n with
    | zero => simp
    | succ n I =>
      intros σ
      simp only [liftn, Subst.liftn]
      rw [<-to_subst_lift]
      rw [I]
}

theorem Subst.liftn_lift_commute {σ: Subst}
  : σ.lift.liftn n = (σ.liftn n).lift 
  := by induction n <;> simp [*]

theorem Subst.liftn_commute {σ: Subst}
  : (σ.liftn m).liftn n = (σ.liftn n).liftn m  
  := by induction n <;> simp [liftn, Subst.liftn_lift_commute, *]

theorem Subst.lift_liftn_merge {n: Nat} {σ: Subst}:
  (σ.liftn n).lift = σ.liftn (n + 1) := rfl

theorem Subst.liftn_merge_outer (m: Nat)
  : (n: Nat) -> {σ: Subst} -> (σ.liftn m).liftn n = σ.liftn (n + m) 
  := by induction m <;> simp [liftn, <-liftn_lift_commute, *]

theorem Subst.liftn_merge
  : (m n: Nat) -> {σ: Subst} -> (σ.liftn m).liftn n  = σ.liftn (m + n) 
  := by intros; simp [liftn_merge_outer, Nat.add_comm]

theorem Subst.liftn_base_nil: (base: Nat) -> (σ: Subst) -> 
  (v: Nat) -> v < base ->
  σ.liftn base v = Untyped.var v := by {
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
      rfl
      rw [<-Nat.succ_lt_succ_is_lt]
      apply H
}

theorem Subst.liftn_above_wk: (base: Nat) -> (σ: Subst) -> 
  (v: Nat) -> base ≤ v ->
  σ.liftn base v = (σ (v - base)).wkn base := by {
    intros base;
    induction base with
    | zero => simp
    | succ base I =>
      intros σ v H;
      simp only [liftn, Untyped.wkn, Wk.wkn]
      cases v with
      | zero => cases H
      | succ v => 
        simp only [lift, wk1, Untyped.wk1]
        rw [Nat.succ_sub_succ_eq_sub]
        rw [<-Wk.step_is_comp_wk1]
        rw [<-Untyped.wk_composes]
        rw [I]
        rfl
        apply Nat.le_of_succ_le_succ
        apply H
}

@[simp]
def Untyped.subst: Untyped -> Subst -> Untyped
  | var v, σ => σ v
  | const c, σ => const c
  | unary k t, σ => unary k (t.subst σ)
  | let_bin k t, σ => let_bin k (t.subst (σ.liftn 2))
  | bin k l r, σ => bin k (l.subst σ) (r.subst σ)
  | abs k A t, σ => abs k (A.subst σ) (t.subst σ.lift)
  | tri k A l r, σ => tri k (A.subst σ) (l.subst σ) (r.subst σ)
  | cases k K d l r, σ => 
    cases k (K.subst σ.lift) (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)

theorem Subst.lift_var: {n v: Nat} -> {σ: Subst} -> 
  (σ.liftn (n + 1)) (Wk.var (Wk.wknth n) v) 
  = (σ.liftn n v).wknth n
  := by {
    intros n v σ;
    cases Nat.le_or_lt v n with
    | inl Hnv =>
      rw [liftn_base_nil _ _ _ Hnv]
      rw [liftn_base_nil]
      simp only [Untyped.wknth, Untyped.wk]
      rw [Wk.wknth_small Hnv]
      exact Nat.le_step Hnv
    | inr Hnv =>
      rw [liftn_above_wk _ _ _ Hnv]
      rw [liftn_above_wk]
      simp only [
        Untyped.wknth, Untyped.wk, Untyped.wkn, Wk.wkn, Nat.add]
      rw [Wk.wknth_big Hnv]
      rw [Nat.succ_sub_succ_eq_sub]
      rw [Untyped.wk_composes]
      rw [Untyped.wk_coherent Wk.wknth_wkn_equiv]
      rfl
      rw [Wk.wknth_big Hnv]
      exact Nat.succ_le_succ Hnv
  }

theorem Untyped.liftn_wk {u: Untyped}: {σ: Subst} -> (n: Nat) ->
  (u.wknth n).subst (σ.liftn (n + 1))  =
  (u.subst (σ.liftn n)).wknth n
  := by {
    unfold Wk.wk1
    induction u with
    | var v =>
      intros σ n;
      simp only [subst, Subst.lift_var]
    | const c => simp
    | unary k t I => 
      intros σ n
      simp only [wknth] at I
      simp only [wknth, wk, subst, I]
    | let_bin k e I =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at I
      rw [I]
      simp
    | bin k l r Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [Il, Ir]
    | abs k A t IA It => 
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [
        IA, 
        Wk.lift_wknth_merge, 
        Subst.lift_liftn_merge, 
        Subst.lift_liftn_merge,
        It]
      exact 0 -- TODO: why?
    | tri k A l r IA Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [IA, Il, Ir]
    | cases k K d l r IK Id Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [Id]
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IK, Il, Ir]
      exact 0 -- TODO: why?
  }

theorem Subst.lift_wk {u: Untyped}: {σ: Subst} ->
  u.wk1.subst (σ.lift) = (u.subst σ).wk1 := by {
    intros σ;
    apply Untyped.liftn_wk 0
}

def Subst.comp (σ ρ: Subst): Subst
  | v => (ρ v).subst σ

@[simp] theorem Subst.lift_comp {ρ σ: Subst}: 
  comp (lift ρ) (lift σ) = lift (comp ρ σ) := by {
    funext v;
    cases v with
    | zero => simp [comp]
    | succ v => simp only [lift_succ, comp, wk1, lift_wk]
  }

@[simp] theorem Subst.liftn_comp {ρ σ: Subst} {l: Nat}: 
  comp (liftn ρ l) (liftn σ l) = liftn (comp ρ σ) l 
  := by induction l <;> simp [*]

@[simp] theorem Untyped.subst_composes (u: Untyped):
  (σ ρ: Subst) -> (u.subst ρ).subst σ = u.subst (σ.comp ρ)
  := by {
  induction u;
  case var => simp [Subst.comp]
  all_goals simp [*]
}

@[simp] theorem Subst.comp_assoc {ρ σ τ: Subst}:
  comp ρ (comp σ τ) = comp (comp ρ σ) τ := by {
    funext v;
    simp [comp]
  }

@[simp] theorem Subst.subst_wk_compat: {u: Untyped} -> {ρ: Wk} ->
  u.subst ρ.to_subst = u.wk ρ := by {
  intro u;
  induction u <;> {
    simp only [
      Untyped.subst, 
      Wk.to_subst_lift, Wk.to_subst_liftn, 
      *]
    rfl
  }
}

def subst_maps (n m: Nat) (σ: Subst) := ∀v, v < m -> Untyped.fv (σ v) ≤ n

def Subst.wk_bounds {ρ: Wk} {n m: Nat}: 
  ρ.maps n m -> subst_maps n m ρ.to_subst := by {
  intros Hρ v Hv;
  simp only [Wk.to_subst, Untyped.fv]
  exact Hρ _ Hv
}

def Subst.wk1_subst: {σ: Subst} -> {n m: Nat} ->
  subst_maps n m σ -> subst_maps (n + 1) m (wk1 σ) := by {
    intros σ n m Hσ v Hv;
    simp only [Untyped.fv, wk1]
    apply Nat.le_trans Untyped.fv_wk1;
    apply Nat.succ_le_succ;
    exact Hσ _ Hv
  }

def Subst.lift_subst: {σ: Subst} -> {n m: Nat} -> 
  subst_maps n m σ -> subst_maps (n + 1) (m + 1) (lift σ) := by {
    intros σ n m Hσ v Hv;
    cases v with
    | zero =>
      simp only [Untyped.fv]
      exact Nat.succ_le_succ (Nat.zero_le _)
    | succ v =>
      simp only [Untyped.fv, lift]
      apply wk1_subst Hσ
      apply Nat.le_of_succ_le_succ
      exact Hv
  }

def Subst.liftn_subst:  {l n m: Nat} -> {σ: Subst} ->
  subst_maps n m σ -> subst_maps (n + l) (m + l) (σ.liftn l) := by {
    intro l;
    induction l with
    | zero => intros n m σ Hσ; exact Hσ
    | succ l I =>
      intros n m σ Hσ;
      simp only [liftn]
      exact Subst.lift_subst (I Hσ)
  }

--TODO: simplify
theorem Untyped.subst_bounds: 
  {u: Untyped} -> {σ: Subst} -> {n m: Nat} -> 
  fv u ≤ m -> subst_maps n m σ -> fv (u.subst σ) ≤ n := by {
  intro u;
  induction u with
  | var v => 
    intros σ n m Hv Hσ; 
    simp at Hv
    exact Hσ _ Hv
  | const c => 
    intros σ n m Hv Hσ; 
    simp only [fv, subst]
    apply Nat.zero_le
  | unary k t I =>
    intros σ n m Hv Hσ;
    simp only [fv, subst];
    exact I Hv Hσ
  | let_bin k e I =>
    simp only [fv, subst, Nat.le_sub_is_le_add]
    intros σ n m Hv Hσ;
    exact I Hv (Subst.liftn_subst Hσ)
  | bin k l r Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split]
    intro ⟨Hl, Hr⟩
    intro Hσ
    exact ⟨Il Hl Hσ, Ir Hr Hσ⟩
  | abs k A s IA Is =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HA, Hs⟩
    intro Hσ
    --TODO: move lift_subst to subst_maps?
    exact ⟨IA HA Hσ, Is Hs (Subst.lift_subst Hσ)⟩
  | tri k A l r IA Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split]
    intro ⟨HA, Hl, Hr⟩
    intro Hσ
    exact ⟨IA HA Hσ, Il Hl Hσ, Ir Hr Hσ⟩
  | cases k K d l r IK Id Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, Hd, Hl, Hr⟩
    intro Hσ
    exact ⟨
      IK HK (Subst.lift_subst Hσ), 
      Id Hd Hσ, Il Hl (Subst.lift_subst Hσ), 
      Ir Hr (Subst.lift_subst Hσ)
      ⟩
}

@[simp]
def Untyped.to_subst (u: Untyped): Subst
  | 0 => u
  | Nat.succ n => Untyped.var n

@[simp]
def Untyped.to_alpha (u: Untyped): Subst
  | 0 => u
  | Nat.succ n => Untyped.var (Nat.succ n)

def Untyped.to_alpha_lift {u: Untyped}: u.to_alpha = u.to_subst.comp (Wk.wknth 1).to_subst 
  := by {
    funext v;
    cases v with
    | zero => simp [Subst.comp]
    | succ v =>
      simp only [Subst.comp]
      rfl
  }

@[simp]
def Untyped.to_subst_succ {u: Untyped}: u.to_subst (n + 1) = var n := rfl

def Untyped.subst0: Untyped -> Untyped -> Untyped
  | u, v => u.subst v.to_subst

def Untyped.alpha0: Untyped -> Untyped -> Untyped
  | u, v => u.subst v.to_alpha

def Untyped.alpha0_lift_comp {u v: Untyped}: 
  u.alpha0 v = u.subst (v.to_subst.comp (Wk.wknth 1).to_subst) := by {
    simp only [alpha0]
    rw [to_alpha_lift]
  }

def Untyped.alpha0_lift {u v: Untyped}:
  u.alpha0 v = (u.wknth 1).subst0 v := by {
    rw [Untyped.alpha0_lift_comp]
    simp only [subst0]
    rw [<-Untyped.subst_composes]
    rw [Subst.subst_wk_compat]
    rfl
  }

@[simp]
def Untyped.subst0_def {u v: Untyped}: 
  u.subst0 v = u.subst v.to_subst := rfl

@[simp]
def Untyped.alpha0_def {u v: Untyped}: 
  u.alpha0 v = u.subst v.to_alpha := rfl

def Untyped.substnth: Untyped -> Nat -> Untyped -> Untyped
  | u, n, v => u.subst (v.to_subst.liftn n)

def Untyped.alphanth: Untyped -> Nat -> Untyped -> Untyped
  | u, n, v => u.subst (v.to_alpha.liftn n)

@[simp]
def Untyped.substnth_def {u v: Untyped} {l}:
  u.substnth l v = u.subst (v.to_subst.liftn l) := rfl

@[simp]
def Untyped.alphanth_def {u v: Untyped} {l}:
  u.alphanth l v = u.subst (v.to_alpha.liftn l) := rfl

def Untyped.substnth_wknth {u: Untyped}: {v: Untyped} -> {l: Nat} ->
  (u.wknth l).substnth l v = u := by {
  induction u <;> intros v l;
  case var n =>
    simp only [substnth, wknth, wk, subst]
    cases (Nat.le_or_lt n l) with
    | inl H =>
      rw [Subst.liftn_base_nil] <;>
      rw [Wk.wknth_small H] <;>
      exact H
    | inr H =>
      rw [Subst.liftn_above_wk]
      rw [Wk.wknth_big H]
      rw [Nat.succ_sub_gt H]
      rw [to_subst_succ]
      simp [Nat.add_sub_self_gt H]
      rw [Wk.wknth_big H]
      exact Nat.le_succ_of_le H

  all_goals (
    simp only [substnth, subst]
    repeat first 
    | rw [Wk.lift_wknth_merge] 
    | rw [Wk.liftn_wknth_merge] 
    | rw [Subst.lift_liftn_merge]
    | rw [Subst.liftn_merge]
    try simp only [<-substnth_def, <-wknth_def]
    try simp only [*]
    repeat exact 0
  )
}

def Untyped.subst0_wk1 {u: Untyped} {v: Untyped}:
  u.wk1.subst0 v = u := @Untyped.substnth_wknth u v 0

def Untyped.alpha0_wk1 {u: Untyped} {v: Untyped}:
  u.wk1.alpha0 v = u.wk1 := by {
    rw [Untyped.alpha0_lift]
    simp only [wknth, wk1, Wk.wknth, Wk.liftn, Wk.wk1, Wk.comp, wk_composes]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-wk_composes]
    rw [<-wk1_def]
    rw [subst0_wk1]
  }

def Untyped.to_alpha_wk1 {u: Untyped}:
  u.to_alpha.comp Wk.wk1.to_subst = Wk.wk1.to_subst := by {
    funext v;
    cases v with
    | zero => rfl
    | succ v =>
      simp [Subst.comp, Nat.add_succ]
  }

def Untyped.alphanth_wknth {u v: Untyped} {l: Nat}:
  (u.wknth l).alphanth l v = u.wknth l := by {
    simp only [wknth, Wk.wknth, alphanth]
    rw [<-Subst.subst_wk_compat]
    rw [subst_composes]
    rw [<-Wk.to_subst_liftn]
    rw [Subst.liftn_comp]
    rw [to_alpha_wk1]
  }

theorem Subst.subst0_subst_composes {σ: Subst} {u: Untyped}:
  Subst.comp σ u.to_subst = 
  Subst.comp (u.subst σ).to_subst σ.lift := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      Untyped.to_subst, 
      Untyped.subst]
  | succ v =>
    simp only [
      comp,
      Untyped.subst,
      Subst.lift,
      Subst.wk1
      ];
    rw [<-Untyped.subst0_def]
    rw [Untyped.subst0_wk1]
}

--TODO: rewrite as application of subst0_subst_composes with appropriate lemmas
theorem Subst.subst0_wk_composes {ρ: Wk} {u: Untyped}:
  Subst.comp ρ.to_subst u.to_subst = 
  Subst.comp (u.wk ρ).to_subst ρ.lift.to_subst := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      Untyped.to_subst, 
      Wk.to_subst, 
      Wk.var, 
      Untyped.subst]
    apply Subst.subst_wk_compat
  | succ v =>
    simp only [
      comp,
      Untyped.to_subst,
      Wk.to_subst,
      Wk.var,
      Untyped.subst]
    rfl
}

theorem Untyped.subst0_wk {u v: Untyped}:
  {ρ: Wk} ->
  (u.subst0 v).wk ρ = (u.wk ρ.lift).subst0 (v.wk ρ) := by {
    intros ρ;
    simp only [<-Subst.subst_wk_compat, subst0]
    simp only [subst_composes]
    rw [Subst.subst0_wk_composes]
    simp only [Subst.subst_wk_compat]
  }

theorem Untyped.subst0_subst {u v: Untyped} {σ: Subst}:
  (u.subst0 v).subst σ = (u.subst σ.lift).subst0 (v.subst σ) := by {
    simp only [subst0]
    simp only [subst_composes]
    rw [Subst.subst0_subst_composes]
  }