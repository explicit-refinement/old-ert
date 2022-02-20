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

def RawWk.to_subst_lift {σ: RawWk}: 
  (to_subst σ).lift = to_subst σ.lift := by {
  funext v;
  cases v with
  | zero => simp [RawSubst.lift]
  | succ n => simp [RawSubst.lift, RawSubst.wk1]
}

@[simp]
def RawSubst.lift_succ (σ: RawSubst):
  σ.lift (Nat.succ n) = wk1 σ n := rfl

@[simp]
def RawSubst.lift_zero (σ: RawSubst):
  σ.lift 0 = RawUntyped.var 0 := rfl

@[simp]
def RawSubst.liftn: (σ: RawSubst) -> (l: Nat) -> RawSubst
  | σ, 0 => σ
  | σ, Nat.succ l => (σ.liftn l).lift

def RawWk.to_subst_liftn: {n: Nat} -> {σ: RawWk} ->
  (to_subst σ).liftn n = to_subst (σ.liftn n) := by {
    intro n;
    induction n with
    | zero => simp
    | succ n I =>
      intros σ
      simp only [liftn, RawSubst.liftn]
      rw [<-to_subst_lift]
      rw [I]
}

theorem RawSubst.liftn_lift_commute {σ: RawSubst}
  : σ.lift.liftn n = (σ.liftn n).lift 
  := by induction n <;> simp [*]

theorem RawSubst.liftn_commute {σ: RawSubst}
  : (σ.liftn m).liftn n = (σ.liftn n).liftn m  
  := by induction n <;> simp [liftn, RawSubst.liftn_lift_commute, *]

theorem RawSubst.lift_liftn_merge {n: Nat} {σ: RawSubst}:
  (σ.liftn n).lift = σ.liftn (n + 1) := rfl

theorem RawSubst.liftn_merge_outer (m: Nat)
  : (n: Nat) -> {σ: RawSubst} -> (σ.liftn m).liftn n = σ.liftn (n + m) 
  := by induction m <;> simp [liftn, <-liftn_lift_commute, *]

theorem RawSubst.liftn_merge
  : (m n: Nat) -> {σ: RawSubst} -> (σ.liftn m).liftn n  = σ.liftn (m + n) 
  := by intros; simp [liftn_merge_outer, Nat.add_comm]

theorem RawSubst.liftn_base_nil: (base: Nat) -> (σ: RawSubst) -> 
  (v: Nat) -> v < base ->
  σ.liftn base v = RawUntyped.var v := by {
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

theorem RawSubst.liftn_above_wk: (base: Nat) -> (σ: RawSubst) -> 
  (v: Nat) -> base ≤ v ->
  σ.liftn base v = (σ (v - base)).wkn base := by {
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
        rfl
        apply Nat.le_of_succ_le_succ
        apply H
}

@[simp]
def RawUntyped.subst: RawUntyped -> RawSubst -> RawUntyped
  | var v, σ => σ v
  | const c, σ => const c
  | unary k t, σ => unary k (t.subst σ)
  | let_bin k t, σ => let_bin k (t.subst (σ.liftn 2))
  | bin k l r, σ => bin k (l.subst σ) (r.subst σ)
  | abs k A t, σ => abs k (A.subst σ) (t.subst σ.lift)
  | tri k A l r, σ => tri k (A.subst σ) (l.subst σ) (r.subst σ)
  | cases k K d l r, σ => 
    cases k (K.subst σ.lift) (d.subst σ) (l.subst σ) (r.subst σ)

theorem RawSubst.lift_var: {n v: Nat} -> {σ: RawSubst} -> 
  (σ.liftn (n + 1)) (RawWk.var (RawWk.wknth n) v) 
  = (σ.liftn n v).wknth n
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
      rfl
      rw [RawWk.wknth_big Hnv]
      exact Nat.succ_le_succ Hnv
  }

theorem RawUntyped.liftn_wk {u: RawUntyped}: {σ: RawSubst} -> (n: Nat) ->
  (u.wknth n).subst (σ.liftn (n + 1))  =
  (u.subst (σ.liftn n)).wknth n
  := by {
    unfold RawWk.wk1
    induction u with
    | var v =>
      intros σ n;
      simp only [subst, RawSubst.lift_var]
    | const c => simp
    | unary k t I => 
      intros σ n
      simp only [wknth] at I
      simp only [wknth, wk, subst, I]
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
      simp only [wknth] at *
      rw [Il, Ir]
    | abs k A t IA It => 
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [
        IA, 
        RawWk.lift_wknth_merge, 
        RawSubst.lift_liftn_merge, 
        RawSubst.lift_liftn_merge,
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
      rw [Id, Il, Ir]
      rw [RawWk.lift_wknth_merge]
      rw [RawSubst.lift_liftn_merge]
      rw [RawSubst.lift_liftn_merge]
      rw [IK]
      exact 0 -- TODO: why?
  }

theorem RawSubst.lift_wk {u: RawUntyped}: {σ: RawSubst} ->
  u.wk1.subst (σ.lift) = (u.subst σ).wk1 := by {
    intros σ;
    apply RawUntyped.liftn_wk 0
}

def RawSubst.comp (σ ρ: RawSubst): RawSubst
  | v => (ρ v).subst σ

@[simp] theorem RawSubst.lift_comp {ρ σ: RawSubst}: 
  comp (lift ρ) (lift σ) = lift (comp ρ σ) := by {
    funext v;
    cases v with
    | zero => simp [comp]
    | succ v => simp only [lift_succ, comp, wk1, lift_wk]
  }

@[simp] theorem RawUntyped.subst_composes (u: RawUntyped):
  (σ ρ: RawSubst) -> (u.subst ρ).subst σ = u.subst (σ.comp ρ)
  := by {
  induction u;
  case var => simp [RawSubst.comp]
  all_goals simp [*]
}

@[simp] theorem RawSubst.comp_assoc {ρ σ τ: RawSubst}:
  comp ρ (comp σ τ) = comp (comp ρ σ) τ := by {
    funext v;
    simp [comp]
  }

@[simp] theorem RawSubst.subst_wk_compat: {u: RawUntyped} -> {ρ: RawWk} ->
  u.subst ρ.to_subst = u.wk ρ := by {
  intro u;
  induction u <;> {
    simp only [
      RawUntyped.subst, 
      RawWk.to_subst_lift, RawWk.to_subst_liftn, 
      *]
    rfl
  }
}

def subst_maps (n m: Nat) (σ: RawSubst) := ∀v, v < m -> RawUntyped.fv (σ v) ≤ n

def RawSubst.wk_bounds {n m: Nat}: 
  wk_maps n m ρ -> subst_maps n m (RawWk.to_subst ρ) := by {
  intros Hρ v Hv;
  simp only [RawWk.to_subst, RawUntyped.fv]
  exact Hρ _ Hv
}

def RawSubst.wk1_subst: {σ: RawSubst} -> {n m: Nat} ->
  subst_maps n m σ -> subst_maps (n + 1) m (wk1 σ) := by {
    intros σ n m Hσ v Hv;
    simp only [RawUntyped.fv, wk1]
    apply Nat.le_trans RawUntyped.fv_wk1;
    apply Nat.succ_le_succ;
    exact Hσ _ Hv
  }

def RawSubst.lift_subst: {σ: RawSubst} -> {n m: Nat} -> 
  subst_maps n m σ -> subst_maps (n + 1) (m + 1) (lift σ) := by {
    intros σ n m Hσ v Hv;
    cases v with
    | zero =>
      simp only [RawUntyped.fv]
      exact Nat.succ_le_succ (Nat.zero_le _)
    | succ v =>
      simp only [RawUntyped.fv, lift]
      apply wk1_subst Hσ
      apply Nat.le_of_succ_le_succ
      exact Hv
  }

def RawSubst.liftn_subst:  {l n m: Nat} -> {σ: RawSubst} ->
  subst_maps n m σ -> subst_maps (n + l) (m + l) (σ.liftn l) := by {
    intro l;
    induction l with
    | zero => intros n m σ Hσ; exact Hσ
    | succ l I =>
      intros n m σ Hσ;
      simp only [liftn]
      exact RawSubst.lift_subst (I Hσ)
  }

structure Subst (n m: Nat) := (val: RawSubst) (p: subst_maps n m val)

def Wk.to_subst {n m: Nat} (ρ: Wk n m): Subst n m :=
  Subst.mk (RawWk.to_subst ρ.val) (RawSubst.wk_bounds ρ.p)

--TODO: simplify
theorem RawUntyped.subst_bounds: 
  {u: RawUntyped} -> {σ: RawSubst} -> {n m: Nat} -> 
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
    exact I Hv (RawSubst.liftn_subst Hσ)
  | bin k l r Il Ir =>
    intros σ n m;
    simp only [RawUntyped.fv, Nat.max_r_le_split]
    intro ⟨Hl, Hr⟩
    intro Hσ
    exact ⟨Il Hl Hσ, Ir Hr Hσ⟩
  | abs k A s IA Is =>
    intros σ n m;
    simp only [RawUntyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HA, Hs⟩
    intro Hσ
    --TODO: move lift_subst to subst_maps?
    exact ⟨IA HA Hσ, Is Hs (RawSubst.lift_subst Hσ)⟩
  | tri k A l r IA Il Ir =>
    intros σ n m;
    simp only [RawUntyped.fv, Nat.max_r_le_split]
    intro ⟨HA, Hl, Hr⟩
    intro Hσ
    exact ⟨IA HA Hσ, Il Hl Hσ, Ir Hr Hσ⟩
  | cases k K d l r IK Id Il Ir =>
    intros σ n m;
    simp only [RawUntyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, Hd, Hl, Hr⟩
    intro Hσ
    exact ⟨IK HK (RawSubst.lift_subst Hσ), Id Hd Hσ, Il Hl Hσ, Ir Hr Hσ⟩
}

def Untyped.subst (σ: Subst n m) (u: Untyped m): Untyped n :=
  Untyped.mk (u.val.subst σ.val) (RawUntyped.subst_bounds u.p σ.p)

@[simp]
def RawUntyped.to_subst (u: RawUntyped): RawSubst
  | 0 => u
  | Nat.succ n => RawUntyped.var n

--@[simp]
def Untyped.to_subst (u: Untyped n): Subst n (n + 1) :=
  Subst.mk (u.val.to_subst) (by {
    intros v Hv;
    cases v with
    | zero => exact u.p
    | succ v => exact Nat.lt_of_succ_lt_succ Hv
  })

def RawUntyped.subst0: RawUntyped -> RawUntyped -> RawUntyped
  | u, v => u.subst v.to_subst

def RawUntyped.subst0_wk1 {u: RawUntyped}: {v: RawUntyped} ->
  u.wk1.subst0 v = u := by {
    induction u <;> intro v;
    case var n =>
      simp [subst0]
      --TODO: this is a really strange hack... think about it...
      apply Nat.succ_match_simp
      apply v

    repeat sorry
  }

@[simp]
def RawUntyped.subst0_def {u v: RawUntyped}: 
  u.subst0 v = u.subst v.to_subst := rfl

theorem RawSubst.subst0_subst_composes {σ: RawSubst} {u: RawUntyped}:
  RawSubst.comp σ u.to_subst = 
  RawSubst.comp (u.subst σ).to_subst σ.lift := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      RawUntyped.to_subst, 
      RawUntyped.subst]
  | succ v =>
    simp only [
      comp,
      RawUntyped.subst,
      RawSubst.lift,
      RawSubst.wk1
      ];
    rw [<-RawUntyped.subst0_def]
    rw [RawUntyped.subst0_wk1]
}

--TODO: rewrite as application of subst0_subst_composes with appropriate lemmas
theorem RawSubst.subst0_wk_composes {ρ: RawWk} {u: RawUntyped}:
  RawSubst.comp ρ.to_subst u.to_subst = 
  RawSubst.comp (u.wk ρ).to_subst ρ.lift.to_subst := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      RawUntyped.to_subst, 
      RawWk.to_subst, 
      RawWk.var, 
      RawUntyped.subst]
    apply RawSubst.subst_wk_compat
  | succ v =>
    simp only [
      comp,
      RawUntyped.to_subst,
      RawWk.to_subst,
      RawWk.var,
      RawUntyped.subst]
    rfl
}

theorem RawUntyped.subst0_wk {u v: RawUntyped}:
  {ρ: RawWk} ->
  (u.subst0 v).wk ρ = (u.wk ρ.lift).subst0 (v.wk ρ) := by {
    intros ρ;
    simp only [<-RawSubst.subst_wk_compat, subst0]
    simp only [subst_composes]
    rw [RawSubst.subst0_wk_composes]
    simp only [RawSubst.subst_wk_compat]
  }

theorem RawUntyped.subst0_subst {u v: RawUntyped} {σ: RawSubst}:
  (u.subst0 v).subst σ = (u.subst σ.lift).subst0 (v.subst σ) := by {
    simp only [subst0]
    simp only [subst_composes]
    rw [RawSubst.subst0_subst_composes]
  }