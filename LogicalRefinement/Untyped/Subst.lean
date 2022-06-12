import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Untyped.Wk
import LogicalRefinement.Tactics

def Subst := Nat -> Term

@[simp]
def Subst.id: Subst := Term.var

def Subst.wk1 (σ: Subst): Subst :=
  λv => Term.wk1 (σ v)

@[simp]
def Wk.to_subst (σ: Wk): Subst
  | v => Term.var (σ.var v)

instance Wk.wkSubstCoe: Coe Wk Subst where
  coe := Wk.to_subst

def Subst.lift (σ: Subst): Subst
  | 0 => Term.var 0
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
  σ.lift 0 = Term.var 0 := rfl

@[simp]
def Subst.liftn (σ: Subst): Nat -> Subst
  | 0 => σ
  | Nat.succ l => (σ.liftn l).lift

@[simp]
def Subst.liftn_succ {σ: Subst} {l}: σ.liftn (Nat.succ l) = (σ.liftn l).lift := rfl

def Subst.liftn_add {σ: Subst}: σ.liftn m (v + m) = (σ v).wkn m 
:= by {
  induction m with
  | zero => simp
  | succ m I =>
    simp only [liftn]
    rw [Nat.add_succ]
    rw [lift_succ]
    simp only [wk1]
    simp only [Term.wkn, Wk.wkn]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-Term.wk_composes]
    rw [I]
    rfl
}

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

theorem Subst.liftn_merge_outer {m: Nat}
  : {n: Nat} -> {σ: Subst} -> (σ.liftn m).liftn n = σ.liftn (n + m) 
  := by induction m <;> simp [liftn, <-liftn_lift_commute, *]

theorem Subst.liftn_merge
  : {m n: Nat} -> {σ: Subst} -> (σ.liftn m).liftn n  = σ.liftn (m + n) 
  := by intros; simp [liftn_merge_outer, Nat.add_comm]

theorem Subst.liftn_base_nil {σ: Subst}: {base v: Nat} -> 
  v < base -> σ.liftn base v = Term.var v := by {
  intros base;
  revert σ;
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

theorem Subst.liftn_above_wk {σ: Subst}: {base v: Nat} -> 
  base ≤ v -> σ.liftn base v = (σ (v - base)).wkn base := by {
    intros base;
    revert σ;
    induction base with
    | zero => simp
    | succ base I =>
      intros σ v H;
      simp only [liftn, Term.wkn, Wk.wkn]
      cases v with
      | zero => cases H
      | succ v => 
        simp only [lift, wk1, Term.wk1]
        rw [Nat.succ_sub_succ_eq_sub]
        rw [<-Wk.step_is_comp_wk1]
        rw [<-Term.wk_composes]
        rw [I]
        rfl
        apply Nat.le_of_succ_le_succ
        apply H
}

@[simp]
def Term.subst: Term -> Subst -> Term
  | var v, σ => σ v
  | const c, _ => const c
  | unary k t, σ => unary k (t.subst σ)
  | let_bin k P e e', σ => 
    let_bin k (P.subst σ) (e.subst σ) (e'.subst (σ.liftn 2))
  | let_bin_beta k P l r e', σ => 
    let_bin_beta k (P.subst σ) (l.subst σ) (r.subst σ) (e'.subst (σ.liftn 2))
  | bin k l r, σ => bin k (l.subst σ) (r.subst σ)
  | abs k A t, σ => abs k (A.subst σ) (t.subst σ.lift)
  | tri k A l r, σ => tri k (A.subst σ) (l.subst σ) (r.subst σ)
  | ir k x y P, σ => ir k (x.subst σ) (y.subst σ) (P.subst σ.lift)
  | cases k K d l r, σ => 
    cases k (K.subst σ) (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)
  | nr k K e z s, σ =>
    nr k (K.subst σ.lift) (e.subst σ) (z.subst σ) (s.subst (σ.liftn 2))
  | nz k K z s, σ =>
    nz k (K.subst σ.lift) (z.subst σ) (s.subst (σ.liftn 2))

-- TODO: automate
theorem Subst.lift_var: {n v: Nat} -> {σ: Subst} -> 
  (σ.liftn (n + 1)) (Wk.var (Wk.wknth n) v) 
  = (σ.liftn n v).wknth n
  := by {
    intros n v σ;
    cases Nat.le_or_lt v n with
    | inl Hnv =>
      rw [liftn_base_nil Hnv]
      rw [liftn_base_nil]
      simp only [Term.wknth, Term.wk]
      rw [Wk.wknth_small Hnv]
      exact Nat.le_step Hnv
    | inr Hnv =>
      rw [liftn_above_wk Hnv]
      rw [liftn_above_wk]
      simp only [
        Term.wknth, Term.wk, Term.wkn, Wk.wkn, Nat.add]
      rw [Wk.wknth_big Hnv]
      rw [Nat.succ_sub_succ_eq_sub]
      rw [Term.wk_composes]
      rw [Term.wk_coherent Wk.wknth_wkn_equiv]
      rfl
      rw [Wk.wknth_big Hnv]
      exact Nat.succ_le_succ Hnv
  }

--TODO: automate
theorem Term.liftn_wk {u: Term}: {σ: Subst} -> (n: Nat) ->
  (u.wknth n).subst (σ.liftn (n + 1))  =
  (u.subst (σ.liftn n)).wknth n
  := by {
    induction u with
    | var v =>
      intros σ n;
      simp only [subst, Subst.lift_var]
    | const c => simp
    | unary k t I => 
      intros σ n
      simp only [wknth] at I
      simp only [wknth, wk, subst, I]
    | let_bin k P e e' IP Ie Ie' =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [IP, Ie, Ie']
      simp
    | let_bin_beta k P l r e' IP Il Ir Ie' =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [IP, Il, Ir, Ie']
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
    | tri k A l r IA Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [IA, Il, Ir]
    | ir k x y P Ix Iy IP =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [Ix n]
      rw [Iy n]
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IP]
    | cases k K d l r IK Id Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [Id n]
      rw [IK n]
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [Il, Ir]
    | nr k K e z s IK Ie Iz Is =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IK, Ie, Iz, Is]
      simp
    | nz k K z s IK Iz Is =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IK, Iz, Is]
      simp
  }

theorem Subst.lift_wk {u: Term}: {σ: Subst} ->
  u.wk1.subst (σ.lift) = (u.subst σ).wk1 := by {
    intros σ;
    apply Term.liftn_wk 0
}

theorem Subst.liftn_wkn {u: Term} {σ: Subst} {n: Nat}:
  (u.wkn n).subst (σ.liftn n) = (u.subst σ).wkn n := by {
    revert u σ;
    induction n with
    | zero => intros; simp
    | succ n I =>
      intros u σ;
      simp only [Term.wkn_wk1, liftn_succ]
      rw [lift_wk]
      rw [I]
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

@[simp] theorem Subst.lift_id_equiv: Subst.id.lift = Subst.id
  := by funext v; cases v <;> rfl

@[simp] theorem Term.subst_id (u: Term): u.subst Subst.id = u
  := by {
    induction u 
    <;> simp only [*, Subst.lift_id_equiv, Subst.liftn, subst] 
    <;> rfl
  }

@[simp] theorem Term.subst_composes (u: Term):
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

@[simp] theorem Subst.subst_wk_compat: {u: Term} -> {ρ: Wk} ->
  u.subst ρ = u.wk ρ := by {
  intro u;
  induction u <;> {
    intros;
    simp only [
      Term.subst, 
      Wk.to_subst_lift, Wk.to_subst_liftn, 
      *]
    rfl
  }
}

def subst_maps (n m: Nat) (σ: Subst) := ∀v, v < m -> Term.fv (σ v) ≤ n

def Subst.wk_bounds {ρ: Wk} {n m: Nat}: 
  ρ.maps n m -> subst_maps n m ρ := by {
  intros Hρ v Hv;
  simp only [Wk.to_subst, Term.fv]
  exact Hρ _ Hv
}

def Subst.wk1_subst: {σ: Subst} -> {n m: Nat} ->
  subst_maps n m σ -> subst_maps (n + 1) m (wk1 σ) := by {
    intros σ n _ Hσ v Hv;
    simp only [Term.fv, wk1]
    apply Nat.le_trans Term.fv_wk1;
    apply Nat.succ_le_succ;
    exact Hσ _ Hv
  }

def Subst.lift_subst: {σ: Subst} -> {n m: Nat} -> 
  subst_maps n m σ -> subst_maps (n + 1) (m + 1) (lift σ) := by {
    intros σ n m Hσ v Hv;
    cases v with
    | zero =>
      simp only [Term.fv]
      exact Nat.succ_le_succ (Nat.zero_le _)
    | succ v =>
      simp only [Term.fv, lift]
      apply wk1_subst Hσ
      apply Nat.le_of_succ_le_succ
      exact Hv
  }

def Subst.liftn_subst:  {l n m: Nat} -> {σ: Subst} ->
  subst_maps n m σ -> subst_maps (n + l) (m + l) (σ.liftn l) := by {
    intro l;
    induction l with
    | zero => intros _ _ _ Hσ; exact Hσ
    | succ l I =>
      intros n m σ Hσ;
      simp only [liftn]
      exact Subst.lift_subst (I Hσ)
  }

--TODO: simplify, automate
theorem Term.subst_bounds: 
  {u: Term} -> {σ: Subst} -> {n m: Nat} -> 
  fv u ≤ m -> subst_maps n m σ -> fv (u.subst σ) ≤ n := by {
  intro u;
  induction u with
  | var v => 
    intros _ _ _ Hv Hσ; 
    simp at Hv
    exact Hσ _ Hv
  | const c => 
    intros σ n _ _ _; 
    simp only [fv, subst]
    apply Nat.zero_le
  | unary k t I =>
    intros σ n m Hv Hσ;
    simp only [fv, subst];
    exact I Hv Hσ
  | let_bin k P e e' IP Ie Ie' =>
    simp only [fv, subst, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro σ n m ⟨HP, He, He'⟩ Hσ;
    apply And.intro
    exact IP HP Hσ
    apply And.intro
    exact Ie He Hσ
    exact Ie' He' (Subst.liftn_subst Hσ)
  | let_bin_beta k P l r e' IP Il Ir Ie' =>
    simp only [fv, subst, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro σ n m ⟨HP, Hl, Hr, He'⟩ Hσ;
    apply And.intro
    exact IP HP Hσ
    apply And.intro
    exact Il Hl Hσ
    apply And.intro
    exact Ir Hr Hσ
    exact Ie' He' (Subst.liftn_subst Hσ)
  | bin k l r Il Ir =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split]
    intro ⟨Hl, Hr⟩ Hσ
    exact ⟨Il Hl Hσ, Ir Hr Hσ⟩
  | abs k A s IA Is =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HA, Hs⟩ Hσ
    --TODO: move lift_subst to subst_maps?
    exact ⟨IA HA Hσ, Is Hs (Subst.lift_subst Hσ)⟩
  | tri k A l r IA Il Ir =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split]
    intro ⟨HA, Hl, Hr⟩ Hσ
    exact ⟨IA HA Hσ, Il Hl Hσ, Ir Hr Hσ⟩
  | ir k x y P Ix Iy IP =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨Hx, Hy, HP⟩ Hσ
    exact ⟨
      Ix Hx Hσ, 
      Iy Hy Hσ,
      IP HP (Subst.lift_subst Hσ)
      ⟩
  | cases k K d l r IK Id Il Ir =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, Hd, Hl, Hr⟩ Hσ
    exact ⟨
      IK HK Hσ, 
      Id Hd Hσ, Il Hl (Subst.lift_subst Hσ), 
      Ir Hr (Subst.lift_subst Hσ)
      ⟩
  | nr k K e z s IK Ie Iz Is =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, He, Hz, Hs⟩ Hσ
    exact ⟨
      IK HK (Subst.lift_subst Hσ), 
      Ie He Hσ, Iz Hz Hσ, 
      Is Hs (Subst.liftn_subst Hσ)
      ⟩
  | nz k K z s IK Iz Is =>
    intros σ n m;
    simp only [Term.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, Hz, Hs⟩ Hσ
    exact ⟨
      IK HK (Subst.lift_subst Hσ), 
      Iz Hz Hσ, 
      Is Hs (Subst.liftn_subst Hσ)
      ⟩
}

theorem Term.liftn_base {σ: Subst} {base: Nat} {u: Term}: 
  u.fv ≤ base -> u.subst (σ.liftn base) = u := by {
  revert σ base;
  induction u;
  case var =>
    intros
    apply Subst.liftn_base_nil
    assumption

  all_goals (
    simp only [
      fv, Nat.max_r_le_split, subst, Subst.lift_liftn_merge,  Subst.liftn_merge,
      Nat.le_sub_is_le_add, and_imp_decompose
      ]
    intros
    simp only [*]
  )
}

theorem Term.liftn_wk_base {ρ: Wk} {base: Nat} {u: Term}: 
  u.fv ≤ base -> u.wk (ρ.liftn base) = u := by {
    rw [<-Subst.subst_wk_compat]
    rw [<-Wk.to_subst_liftn]
    exact liftn_base
}

theorem Term.lift_base {σ: Subst} {u: Term}: 
  u.fv ≤ 1 -> u.subst (σ.lift) = u := liftn_base

theorem Term.lift_wk_base {ρ: Wk} {u: Term}: 
  u.fv ≤ 1 -> u.wk (ρ.lift) = u := liftn_wk_base

@[simp]
def Term.to_subst (u: Term): Subst
  | 0 => u
  | Nat.succ n => Term.var n

@[simp]
def Term.to_alpha (u: Term): Subst
  | 0 => u
  | Nat.succ n => Term.var (Nat.succ n)

@[simp]
def Term.to_alphanth (u: Term) (n: Nat): Subst :=
  u.to_alpha.liftn n

def Term.to_alphanth_def (u: Term) (n: Nat): u.to_alphanth n = u.to_alpha.liftn n := rfl

def Term.to_alpha_lift {u: Term}: u.to_alpha = u.to_subst.comp (Wk.wknth 1)
  := by {
    funext v;
    cases v with
    | zero => simp [Subst.comp]
    | succ v =>
      simp only [Subst.comp]
      rfl
  }

@[simp]
def Term.to_subst_succ {u: Term}: u.to_subst (n + 1) = var n := rfl

def Term.subst0: Term -> Term -> Term
  | u, v => u.subst v.to_subst

def Term.alpha0: Term -> Term -> Term
  | u, v => u.subst v.to_alpha

def Term.alpha0_wknth_comp {u v: Term}: 
  u.alpha0 v = u.subst (v.to_subst.comp (Wk.wknth 1).to_subst) := by {
    simp only [alpha0]
    rw [to_alpha_lift]
  }

def Term.alpha0_wknth {u v: Term}:
  u.alpha0 v = (u.wknth 1).subst0 v := by {
    rw [Term.alpha0_wknth_comp]
    simp only [subst0]
    rw [<-Term.subst_composes]
    rw [Subst.subst_wk_compat]
    rfl
  }

@[simp]
def Term.subst0_def {u v: Term}: 
  u.subst0 v = u.subst v.to_subst := rfl

@[simp]
def Term.alpha0_def {u v: Term}: 
  u.alpha0 v = u.subst v.to_alpha := rfl

def Term.substnth: Term -> Nat -> Term -> Term
  | u, n, v => u.subst (v.to_subst.liftn n)

def Term.alphanth: Term -> Nat -> Term -> Term
  | u, n, v => u.subst (v.to_alpha.liftn n)

@[simp]
def Term.substnth_def {u v: Term} {l}:
  u.substnth l v = u.subst (v.to_subst.liftn l) := rfl

@[simp]
def Term.alphanth_def {u v: Term} {l}:
  u.alphanth l v = u.subst (v.to_alpha.liftn l) := rfl

-- TODO: this is probably much easier to prove by just 
-- converting to substitution form first...
theorem Term.substnth_wknth {u: Term}: {v: Term} -> {l: Nat} ->
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
  )
}

def Term.subst0_wk1 {u: Term} {v: Term}:
  u.wk1.subst0 v = u := @Term.substnth_wknth u v 0

def Term.alpha0_wk1 {u: Term} {v: Term}:
  u.wk1.alpha0 v = u.wk1 := by {
    rw [Term.alpha0_wknth]
    simp only [wknth, wk1, Wk.wknth, Wk.liftn, Wk.wk1, Wk.comp, wk_composes]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-wk_composes]
    rw [<-wk1_def]
    rw [subst0_wk1]
  }

def Term.to_alpha_wk1 {u: Term}:
  u.to_alpha.comp Wk.wk1.to_subst = Wk.wk1.to_subst := by {
    funext v;
    cases v with
    | zero => rfl
    | succ v =>
      simp [Subst.comp, Nat.add_succ]
  }


def Term.to_alpha_0 {u: Term}: u.to_alpha 0 = u := rfl

@[simp]
def Term.alpha_00 {u: Term}: (var 0).alpha0 u = u := rfl

def Term.to_alpha_succ {u: Term}: u.to_alpha (Nat.succ n) = var (Nat.succ n) := rfl

@[simp]
def Term.alpha_succ: (var (n + 1)).alpha0 u = var (n + 1) := rfl

@[simp]
def Term.subst_to_alpha_succ {u: Term}: 
  (var (n + 1)).subst u.to_alpha = var (n + 1) := rfl

def Term.alphanth_wknth {u v: Term} {l: Nat}:
  (u.wknth l).alphanth l v = u.wknth l := by {
    simp only [wknth, Wk.wknth, alphanth]
    rw [<-Subst.subst_wk_compat]
    rw [subst_composes]
    rw [<-Wk.to_subst_liftn]
    rw [Subst.liftn_comp]
    rw [to_alpha_wk1]
  }

def Term.alphanth_wkn {l: Nat}: {u v: Term} ->
  (u.wkn (l + 1)).alphanth l v = u.wkn (l + 1) := by {
    induction l with
    | zero =>
      intros
      simp only [
        wkn, Wk.wkn, <-Wk.step_is_comp_wk1, Wk.comp_id_right_id, <-wk1_def, alphanth, Subst.liftn,
        <-alpha0_def, alpha0_wk1
      ]
    | succ l I =>
      intros
      simp only [alphanth, Subst.liftn, wkn_wk1]
      rw [Subst.lift_wk]
      rw [<-wkn_wk1]
      rw [<-alphanth_def]
      rw [I]
  }

theorem Subst.subst0_subst_composes {σ: Subst} {u: Term}:
  Subst.comp σ u.to_subst = 
  Subst.comp (u.subst σ).to_subst σ.lift := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      Term.to_subst, 
      Term.subst]
  | succ v =>
    simp only [
      comp,
      Term.subst,
      Subst.lift,
      Subst.wk1
      ];
    rw [<-Term.subst0_def]
    rw [Term.subst0_wk1]
}

--TODO: rewrite as application of subst0_subst_composes with appropriate lemmas
theorem Subst.subst0_wk_composes {ρ: Wk} {u: Term}:
  Subst.comp ρ u.to_subst = 
  Subst.comp (u.wk ρ).to_subst ρ.lift := by {
  funext v;
  cases v with
  | zero => 
    simp only [
      comp, 
      Term.to_subst, 
      Wk.to_subst, 
      Wk.var, 
      Term.subst]
    apply Subst.subst_wk_compat
  | succ v =>
    simp only [
      comp,
      Term.to_subst,
      Wk.to_subst,
      Wk.var,
      Term.subst]
    rfl
}

theorem Term.subst0_wk {u v: Term}:
  {ρ: Wk} ->
  (u.subst0 v).wk ρ = (u.wk ρ.lift).subst0 (v.wk ρ) := by {
    intros ρ;
    simp only [<-Subst.subst_wk_compat, subst0]
    simp only [subst_composes]
    rw [Subst.subst0_wk_composes]
    simp only [Subst.subst_wk_compat]
  }

theorem Term.subst0_subst {u v: Term} {σ: Subst}:
  (u.subst0 v).subst σ = (u.subst σ.lift).subst0 (v.subst σ) := by {
    simp only [subst0]
    simp only [subst_composes]
    rw [Subst.subst0_subst_composes]
  }

theorem Term.liftn_below {u: Term}:
  {n: Nat} -> {σ: Subst} ->
  u.fv ≤ n -> u.subst (σ.liftn n) = u := by {
  induction u;
  case var =>
    intros
    apply Subst.liftn_base_nil
    assumption

  all_goals (
    intros n σ H;
    rename_i' I0 I1 I2 I3;
    simp only [subst, Subst.lift_liftn_merge, Subst.liftn_merge]
    try rw [I0]
    try rw [I1]
    try rw [I2]
    try rw [I3]
    all_goals (
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add] at H
      (try exact H) <;>
      (have ⟨Hh, H⟩ := H) <;>
      (try exact Hh) <;>
      (try exact H) <;>
      (have ⟨Hh, H⟩ := H) <;>
      (try exact Hh) <;>
      (try exact H) <;>
      (have ⟨Hh, H⟩ := H) <;>
      (try exact Hh) <;>
      (try exact H)
    )
  )
}


theorem Term.lift_below {u: Term} {σ: Subst} (H: u.fv ≤ 1): u.subst σ.lift = u 
  := liftn_below H

theorem Term.alphann_comm {u v: Term} {σ: Subst} {n: Nat}:
  v.fv ≤ 1 -> 
  (u.subst (σ.liftn (n + 1))).alphanth n v 
  = (u.alphanth n v).subst (σ.liftn (n + 1)) 
  := by {
    intro H;
    revert n σ v;
    induction u;

    --TODO: clean... a lot...
    case var m =>
      intro v σ n
      cases (Nat.le_or_lt m n) with
      | inl H =>
        intro;
        simp only [alphanth, subst]
        repeat first | rw [Subst.liftn_base_nil] | simp only [subst]
        repeat first | exact H | exact (Nat.le_succ_of_le H)
      | inr H =>
        intro H';
        simp only [alphanth, subst]
        rw [Subst.liftn_above_wk H]
        cases H with
        | refl =>
          simp only [Nat.sub_self, to_alpha_0]
          rw [Subst.liftn_base_nil (Nat.le_refl _)]
          simp only [subst]
          rw [Subst.liftn_above_wk (Nat.le_refl _)]
          simp only [Nat.sub_self, to_alpha_0]
          rw [liftn_base]
          induction m with
          | zero => simp [H']
          | succ m I =>
            simp only [wkn, Wk.wkn]
            simp only [<-Wk.step_is_comp_wk1]
            simp only [<-wk_composes]
            simp only [<-wk1_def]
            apply Nat.le_trans fv_wk1
            apply Nat.succ_le_succ
            exact I
        | step H =>
          rw [Subst.liftn_above_wk (Nat.succ_le_succ H)]
          simp only [Nat.succ_sub_succ_eq_sub]
          simp only [Nat.succ_sub_gt H]
          simp only [to_alpha_succ]
          rw [<-alphanth_def]
          rw [alphanth_wkn]
          simp only [wkn, wk, Wk.wkn_var]
          simp only [subst]
          revert n;
          rename_i m;
          cases m with
          | zero =>
            intro n Hn
            cases Hn
            simp --TODO: nonterminal simp
            simp only [Wk.comp_id_right_id, Subst.wk1, wk1]
          | succ m =>
            intro n Hn
            have R: ∀a b, Nat.succ a + b = Nat.succ (a + b) := by {
              simp [Nat.add_comm, Nat.add_succ]
            };
            rw [R]
            rw [Nat.sub_add_cancel Hn]
            simp only [Subst.liftn_succ, Subst.lift_succ, Subst.wk1]
            rw [Subst.liftn_above_wk Hn]
            simp only [wkn, wk1, wk_composes, Wk.step_is_comp_wk1]
            rfl


    all_goals (
      intro v σ n H;
      simp only [alphanth, subst, Subst.lift_liftn_merge, Subst.liftn_merge]
      try simp only [<-alphanth_def]
      try (rename_i I0; rw [I0 H])
      try (rename_i I1; rw [I1 H])
      try (rename_i I2; rw [I2 H])
      try (rename_i I3; rw [I3 H])
    )
  }


theorem Term.alphann_wk_comm {u v: Term} {ρ: Wk} {n: Nat}:
  v.fv ≤ 1 -> 
  (u.wk (ρ.liftn (n + 1))).alphanth n v 
  = (u.alphanth n v).wk (ρ.liftn (n + 1)) := by {
    intro H;
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_liftn];
    exact alphann_comm H
  }

theorem Term.alpha00_comm {u v: Term} {σ: Subst}:
  v.fv ≤ 1 -> 
  (u.subst σ.lift).alpha0 v 
  = (u.alpha0 v).subst σ.lift
  := @alphann_comm u v σ 0

theorem Term.alpha00_wk_comm {u v: Term} {ρ: Wk}:
  v.fv ≤ 1 -> 
  (u.wk ρ.lift).alpha0 v 
  = (u.alpha0 v).wk ρ.lift
  := by {
    intro H;
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_lift];
    exact alpha00_comm H
  }

theorem Term.tmp_fill {A T: Term} {σ: Subst} (H: T.fv ≤ 1): 
  (T.subst0 A).subst σ = T.subst0 (A.subst σ) := by rw [subst0_subst, lift_below H]

theorem Term.tmp_fill_wk {A T: Term} {ρ: Wk} (H: T.fv ≤ 1):
  (T.subst0 A).wk ρ = T.subst0 (A.wk ρ) := by {
    simp only [<-Subst.subst_wk_compat]
    exact tmp_fill H
  }

-- theorem Term.alpha0_fv {u v: Term}: (u.alpha0 v).fv ≤ Nat.max u.fv v.fv := by {
--   revert v;
--   induction u;
--   case var m =>
--     intro v;
--     cases m with
--     | zero => exact Nat.max_le_r
--     | succ m => exact Nat.max_le_l

--   case cases =>
--     intro v;
--     --TODO: alphanth!
--     sorry

--   repeat sorry
-- }

theorem Term.var2_alpha_subst {σ: Subst} {u: Term}:
  u.fv ≤ 2 ->
  u.to_alpha.comp ((Wk.wknth 1).to_subst.comp σ.lift) =
  (σ.liftn 2).comp (u.to_alpha.comp (Wk.wknth 1)) := by {
  intro Hu;
  funext v;
  cases v with
  | zero =>
    simp only [Subst.comp, Subst.wk1, subst, Wk.var, to_alpha, liftn_below Hu]
  | succ v =>
    simp only [Subst.comp]
    have Hv
      : Wk.to_subst (Wk.wknth 1) (Nat.succ v) = var (v + 1 + 1) 
      := rfl;
    rw [Hv]
    rw [subst_to_alpha_succ]
    simp only [subst, Subst.liftn_add, Subst.lift_succ, Subst.wk1]
    rw [Subst.subst_wk_compat]
    simp only [wk1]
    rw [Term.wk_composes]
    simp only [Wk.comp]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-Term.wk_composes]
    rw [<-Term.wk1_def]
    rw [<-Term.alpha0_def]
    rw [Term.alpha0_wk1]
    simp only [wk1]
    rw [Term.wk_composes]
    rfl
}

theorem Term.let_bin_ty_alpha_subst {σ: Subst} {k: TermKind [0, 0]}:
  (bin k (var 1) (var 0)).to_alpha.comp 
    ((Wk.wknth 1).to_subst.comp σ.lift) =
  (σ.liftn 2).comp 
    ((bin k (var 1) (var 0)).to_alpha.comp (Wk.wknth 1))
  := var2_alpha_subst (by simp)

theorem Term.var2_var1_alpha {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (var 1) =
  ((C.wknth 1).alpha0 (var 1)).subst (σ.liftn 2) := by {
  simp only [alpha0, wknth, <-Subst.subst_wk_compat, subst_composes]
  rw [var2_alpha_subst]
  simp
}

theorem Term.var2_var1_alpha_wk {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (var 1) =
  ((C.wknth 1).alpha0 (var 1)).wk (ρ.liftn 2) := by {
  simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_lift, <-Wk.to_subst_liftn]
  exact var2_var1_alpha
}

theorem Term.var2_const_alpha {C: Term} {σ: Subst} {k: TermKind []}:
  ((C.subst σ.lift).wknth 1).alpha0 (const k) =
  ((C.wknth 1).alpha0 (const k)).subst (σ.liftn 2) := by {
  simp only [alpha0, wknth, <-Subst.subst_wk_compat, subst_composes]
  rw [var2_alpha_subst]
  simp
}

theorem Term.var2_zero_alpha {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 zero =
  ((C.wknth 1).alpha0 zero).subst (σ.liftn 2) := var2_const_alpha

theorem Term.let_bin_ty_alpha {C: Term} {σ: Subst} {k: TermKind [0, 0]}:
  ((C.subst σ.lift).wknth 1).alpha0 (bin k (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (bin k (var 1) (var 0))).subst (σ.liftn 2) := by {
  simp only [alpha0, wknth, <-Subst.subst_wk_compat, subst_composes]
  rw [let_bin_ty_alpha_subst]
}

theorem Term.let_bin_ty_alpha_wk {C: Term} {ρ: Wk} {k: TermKind [0, 0]}:
  ((C.wk ρ.lift).wknth 1).alpha0 (bin k (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (bin k (var 1) (var 0))).wk (ρ.liftn 2) := by {
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_lift, <-Wk.to_subst_liftn]
    exact let_bin_ty_alpha
  }

theorem Term.let_bin_ty_alpha_pair {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (pair (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (pair (var 1) (var 0))).subst (σ.liftn 2) 
  := let_bin_ty_alpha

theorem Term.let_bin_ty_alpha_wk_pair {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (pair (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (pair (var 1) (var 0))).wk (ρ.liftn 2) 
  := let_bin_ty_alpha_wk

theorem Term.let_bin_ty_alpha_elem {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (elem (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (elem (var 1) (var 0))).subst (σ.liftn 2) 
  := let_bin_ty_alpha

theorem Term.let_bin_ty_alpha_wk_elem {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (elem (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (elem (var 1) (var 0))).wk (ρ.liftn 2) 
  := let_bin_ty_alpha_wk

theorem Term.let_bin_ty_alpha_repr {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (repr (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (repr (var 1) (var 0))).subst (σ.liftn 2) 
  := let_bin_ty_alpha

theorem Term.let_bin_ty_alpha_wk_repr {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (repr (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (repr (var 1) (var 0))).wk (ρ.liftn 2) 
  := let_bin_ty_alpha_wk

theorem Term.let_bin_ty_alpha_wit {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (wit (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (wit (var 1) (var 0))).subst (σ.liftn 2) 
  := let_bin_ty_alpha

theorem Term.let_bin_ty_alpha_wk_wit {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (wit (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (wit (var 1) (var 0))).wk (ρ.liftn 2) 
  := let_bin_ty_alpha_wk

  theorem Term.let_bin_ty_alpha_conj {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (dconj (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (dconj (var 1) (var 0))).subst (σ.liftn 2) 
  := let_bin_ty_alpha

theorem Term.let_bin_ty_alpha_wk_conj {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (dconj (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (dconj (var 1) (var 0))).wk (ρ.liftn 2) 
  := let_bin_ty_alpha_wk

theorem Subst.subst00_wknth_id
  : (Term.var 0).to_subst.comp (Wk.wknth 1) = Subst.id
  := by {
    funext v;
    cases v <;> rfl
  }

theorem Term.subst00_wknth (u: Term)
  : (u.wknth 1).subst0 (Term.var 0) = u
  := by {
    simp only [subst0, wknth]
    rw [<-Subst.subst_wk_compat]
    rw [Term.subst_composes]
    rw [Subst.subst00_wknth_id]
    rw [Term.subst_id]
  }

def Term.to_subst01 (u v: Term): Subst
  | 0 => u
  | 1 => v
  | n + 2 => Term.var n

def Term.subst01 (e u v: Term): Term := e.subst (u.to_subst01 v)

theorem Subst.subst01_subst {e u v: Term} (σ: Subst):
  (e.subst01 u v).subst σ 
  = (e.subst (σ.liftn 2)).subst01 (u.subst σ) (v.subst σ)
  := sorry

theorem Wk.subst01_wk {e u v: Term} (ρ: Wk):
  (e.subst01 u v).wk ρ 
  = (e.wk (ρ.liftn 2)).subst01 (u.wk ρ) (v.wk ρ)
  := by {
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_liftn]
    apply Subst.subst01_subst
  }

theorem Term.subst01_def {C l r: Term}:
  C.subst (l.to_subst01 r) = C.subst01 l r 
  := rfl

theorem Subst.subst01_wk1 {l r: Term}:
  (l.to_subst01 r).comp Wk.wk1 = r.to_subst
  := by funext n; cases n <;> rfl

theorem Term.subst01_wk1 {C l r: Term}:
  C.wk1.subst01 l r = C.subst0 r
  := by {
    simp only [
      subst01, wk1, subst0, 
      <-Subst.subst_wk_compat,
      subst_composes
    ]
    exact congr rfl Subst.subst01_wk1
  }

theorem Term.subst01_wk1_wk1 {C l r: Term}:
  C.wk1.wk1.subst01 l r = C
  := by {
    simp only [
      subst01, wk1, subst0, 
      <-Subst.subst_wk_compat,
      subst_composes
    ]
    rw [Subst.comp_assoc]
    rw [<-subst_composes]
    rw [Subst.subst01_wk1]
    rw [Subst.subst_wk_compat]
    exact Term.subst0_wk1
  }

theorem Term.alpha0_subst01_bin {k} {C l r: Term}:
  ((C.wknth 1).alpha0 (bin k (var 1) (var 0))).subst01 r l = C.subst0 (bin k l r)
  := sorry

theorem Term.alpha0_inj_subst {i} {C e: Term}:
  C.subst0 (inj i e) = (C.alpha0 (inj i (var 0))).subst0 e
  := sorry

--TODO: prove subst01 properties...