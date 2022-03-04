import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Untyped.Wk
import LogicalRefinement.Tactics

def Subst := Nat -> Untyped

@[simp]
def Subst.id: Subst := Untyped.var

def Subst.wk1 (σ: Subst): Subst :=
  λv => Untyped.wk1 (σ v)

@[simp]
def Wk.to_subst (σ: Wk): Subst
  | v => Untyped.var (σ.var v)

instance Wk.wkSubstCoe: Coe Wk Subst where
  coe := Wk.to_subst

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
    simp only [Untyped.wkn, Wk.wkn]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-Untyped.wk_composes]
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
  v < base -> σ.liftn base v = Untyped.var v := by {
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
  | let_bin k e e', σ => let_bin k (e.subst σ) (e'.subst (σ.liftn 2))
  | bin k l r, σ => bin k (l.subst σ) (r.subst σ)
  | abs k A t, σ => abs k (A.subst σ) (t.subst σ.lift)
  | tri k A l r, σ => tri k (A.subst σ) (l.subst σ) (r.subst σ)
  | cases k K d l r, σ => 
    cases k (K.subst σ.lift) (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)
  | natrec K e z s, σ =>
    natrec (K.subst σ.lift) (e.subst σ) (z.subst σ) (s.subst (σ.liftn 2))

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
      simp only [Untyped.wknth, Untyped.wk]
      rw [Wk.wknth_small Hnv]
      exact Nat.le_step Hnv
    | inr Hnv =>
      rw [liftn_above_wk Hnv]
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

--TODO: automate
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
    | let_bin k e e' I I' =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [I, I']
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
    | cases k K d l r IK Id Il Ir =>
      intros σ n
      simp only [wknth, wk, subst]
      simp only [wknth] at *
      rw [Id]
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IK, Il, Ir]
    | natrec K e z s IK Ie Iz Is =>
      intros σ n
      simp only [wknth, wk, subst, Wk.liftn_wknth_merge]
      rw [Subst.liftn_merge]
      simp only [wknth] at *
      rw [Wk.lift_wknth_merge]
      rw [Subst.lift_liftn_merge]
      rw [Subst.lift_liftn_merge]
      rw [IK, Ie, Iz, Is]
      simp
  }

theorem Subst.lift_wk {u: Untyped}: {σ: Subst} ->
  u.wk1.subst (σ.lift) = (u.subst σ).wk1 := by {
    intros σ;
    apply Untyped.liftn_wk 0
}

theorem Subst.liftn_wkn {u: Untyped} {σ: Subst} {n: Nat}:
  (u.wkn n).subst (σ.liftn n) = (u.subst σ).wkn n := by {
    revert u σ;
    induction n with
    | zero => intros; simp
    | succ n I =>
      intros u σ;
      simp only [Untyped.wkn_wk1, liftn_succ]
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
  u.subst ρ = u.wk ρ := by {
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
  ρ.maps n m -> subst_maps n m ρ := by {
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

--TODO: simplify, automate
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
  | let_bin k e e' I I' =>
    simp only [fv, subst, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro σ n m ⟨He, He'⟩ Hσ;
    apply And.intro
    exact I He Hσ
    exact I' He' (Subst.liftn_subst Hσ)
  | bin k l r Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split]
    intro ⟨Hl, Hr⟩ Hσ
    exact ⟨Il Hl Hσ, Ir Hr Hσ⟩
  | abs k A s IA Is =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HA, Hs⟩ Hσ
    --TODO: move lift_subst to subst_maps?
    exact ⟨IA HA Hσ, Is Hs (Subst.lift_subst Hσ)⟩
  | tri k A l r IA Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split]
    intro ⟨HA, Hl, Hr⟩ Hσ
    exact ⟨IA HA Hσ, Il Hl Hσ, Ir Hr Hσ⟩
  | cases k K d l r IK Id Il Ir =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, Hd, Hl, Hr⟩ Hσ
    exact ⟨
      IK HK (Subst.lift_subst Hσ), 
      Id Hd Hσ, Il Hl (Subst.lift_subst Hσ), 
      Ir Hr (Subst.lift_subst Hσ)
      ⟩
  | natrec K e z s IK Ie Iz Is =>
    intros σ n m;
    simp only [Untyped.fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
    intro ⟨HK, He, Hz, Hs⟩ Hσ
    exact ⟨
      IK HK (Subst.lift_subst Hσ), 
      Ie He Hσ, Iz Hz Hσ, 
      Is Hs (Subst.liftn_subst Hσ)
      ⟩
}

theorem Untyped.liftn_base {σ: Subst} {base: Nat} {u: Untyped}: 
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

theorem Untyped.liftn_wk_base {ρ: Wk} {base: Nat} {u: Untyped}: 
  u.fv ≤ base -> u.wk (ρ.liftn base) = u := by {
    rw [<-Subst.subst_wk_compat]
    rw [<-Wk.to_subst_liftn]
    exact liftn_base
}

theorem Untyped.lift_base {σ: Subst} {u: Untyped}: 
  u.fv ≤ 1 -> u.subst (σ.lift) = u := liftn_base

theorem Untyped.lift_wk_base {ρ: Wk} {u: Untyped}: 
  u.fv ≤ 1 -> u.wk (ρ.lift) = u := liftn_wk_base

@[simp]
def Untyped.to_subst (u: Untyped): Subst
  | 0 => u
  | Nat.succ n => Untyped.var n

@[simp]
def Untyped.to_alpha (u: Untyped): Subst
  | 0 => u
  | Nat.succ n => Untyped.var (Nat.succ n)

@[simp]
def Untyped.to_alphanth (u: Untyped) (n: Nat): Subst :=
  u.to_alpha.liftn n

def Untyped.to_alphanth_def (u: Untyped) (n: Nat): u.to_alphanth n = u.to_alpha.liftn n := rfl

def Untyped.to_alpha_lift {u: Untyped}: u.to_alpha = u.to_subst.comp (Wk.wknth 1)
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

def Untyped.alpha0_wknth_comp {u v: Untyped}: 
  u.alpha0 v = u.subst (v.to_subst.comp (Wk.wknth 1).to_subst) := by {
    simp only [alpha0]
    rw [to_alpha_lift]
  }

def Untyped.alpha0_wknth {u v: Untyped}:
  u.alpha0 v = (u.wknth 1).subst0 v := by {
    rw [Untyped.alpha0_wknth_comp]
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
  )
}

def Untyped.subst0_wk1 {u: Untyped} {v: Untyped}:
  u.wk1.subst0 v = u := @Untyped.substnth_wknth u v 0

def Untyped.alpha0_wk1 {u: Untyped} {v: Untyped}:
  u.wk1.alpha0 v = u.wk1 := by {
    rw [Untyped.alpha0_wknth]
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


def Untyped.to_alpha_0 {u: Untyped}: u.to_alpha 0 = u := rfl

@[simp]
def Untyped.alpha_00 {u: Untyped}: (var 0).alpha0 u = u := rfl

def Untyped.to_alpha_succ {u: Untyped}: u.to_alpha (Nat.succ n) = var (Nat.succ n) := rfl

@[simp]
def Untyped.alpha_succ: (var (n + 1)).alpha0 u = var (n + 1) := rfl

@[simp]
def Untyped.subst_to_alpha_succ {u: Untyped}: 
  (var (n + 1)).subst u.to_alpha = var (n + 1) := rfl

def Untyped.alphanth_wknth {u v: Untyped} {l: Nat}:
  (u.wknth l).alphanth l v = u.wknth l := by {
    simp only [wknth, Wk.wknth, alphanth]
    rw [<-Subst.subst_wk_compat]
    rw [subst_composes]
    rw [<-Wk.to_subst_liftn]
    rw [Subst.liftn_comp]
    rw [to_alpha_wk1]
  }

def Untyped.alphanth_wkn {l: Nat}: {u v: Untyped} ->
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
  Subst.comp ρ u.to_subst = 
  Subst.comp (u.wk ρ).to_subst ρ.lift := by {
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

theorem Untyped.liftn_below {u: Untyped}:
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

theorem Untyped.alphann_comm {u v: Untyped} {σ: Subst} {n: Nat}:
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
          induction m with
          | zero =>
            intro n Hn
            cases Hn
            simp --TODO: nonterminal simp
            simp only [Wk.comp_id_right_id, Subst.wk1, wk1]
          | succ m I =>
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


theorem Untyped.alphann_wk_comm {u v: Untyped} {ρ: Wk} {n: Nat}:
  v.fv ≤ 1 -> 
  (u.wk (ρ.liftn (n + 1))).alphanth n v 
  = (u.alphanth n v).wk (ρ.liftn (n + 1)) := by {
    intro H;
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_liftn];
    exact alphann_comm H
  }

theorem Untyped.alpha00_comm {u v: Untyped} {σ: Subst}:
  v.fv ≤ 1 -> 
  (u.subst σ.lift).alpha0 v 
  = (u.alpha0 v).subst σ.lift
  := @alphann_comm u v σ 0

theorem Untyped.alpha00_wk_comm {u v: Untyped} {ρ: Wk}:
  v.fv ≤ 1 -> 
  (u.wk ρ.lift).alpha0 v 
  = (u.alpha0 v).wk ρ.lift
  := by {
    intro H;
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_lift];
    exact alpha00_comm H
  }

-- theorem Untyped.alpha0_fv {u v: Untyped}: (u.alpha0 v).fv ≤ Nat.max u.fv v.fv := by {
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

theorem Untyped.var2_alpha_subst {σ: Subst} {u: Untyped}:
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
    rw [Untyped.wk_composes]
    simp only [Wk.comp]
    rw [<-Wk.step_is_comp_wk1]
    rw [<-Untyped.wk_composes]
    rw [<-Untyped.wk1_def]
    rw [<-Untyped.alpha0_def]
    rw [Untyped.alpha0_wk1]
    simp only [wk1]
    rw [Untyped.wk_composes]
    rfl
}

theorem Untyped.let_bin_ty_alpha_subst {σ: Subst} {k: UntypedKind [0, 0]}:
  (bin k (var 1) (var 0)).to_alpha.comp 
    ((Wk.wknth 1).to_subst.comp σ.lift) =
  (σ.liftn 2).comp 
    ((bin k (var 1) (var 0)).to_alpha.comp (Wk.wknth 1))
  := var2_alpha_subst (by simp)

theorem Untyped.let_const_alpha {C: Untyped} {σ: Subst} {k: UntypedKind []}:
  ((C.subst σ.lift).wknth 1).alpha0 (const k) =
  ((C.wknth 1).alpha0 (const k)).subst (σ.liftn 2) := by {
  simp only [alpha0, wknth, <-Subst.subst_wk_compat, subst_composes]
  rw [var2_alpha_subst]
  simp
}

theorem Untyped.let_bin_ty_alpha {C: Untyped} {σ: Subst} {k: UntypedKind [0, 0]}:
  ((C.subst σ.lift).wknth 1).alpha0 (bin k (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (bin k (var 1) (var 0))).subst (σ.liftn 2) := by {
  simp only [alpha0, wknth, <-Subst.subst_wk_compat, subst_composes]
  rw [let_bin_ty_alpha_subst]
}

theorem Untyped.let_bin_ty_alpha_wk {C: Untyped} {ρ: Wk} {k: UntypedKind [0, 0]}:
  ((C.wk ρ.lift).wknth 1).alpha0 (bin k (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (bin k (var 1) (var 0))).wk (ρ.liftn 2) := by {
    simp only [<-Subst.subst_wk_compat, <-Wk.to_subst_lift, <-Wk.to_subst_liftn]
    exact let_bin_ty_alpha
  }

theorem Untyped.let_bin_ty_alpha_pair {C: Untyped} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (pair (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (pair (var 1) (var 0))).subst (σ.liftn 2) := let_bin_ty_alpha

theorem Untyped.let_bin_ty_alpha_wk_pair {C: Untyped} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (pair (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (pair (var 1) (var 0))).wk (ρ.liftn 2) := let_bin_ty_alpha_wk

theorem Untyped.let_bin_ty_alpha_elem {C: Untyped} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (elem (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (elem (var 1) (var 0))).subst (σ.liftn 2) := let_bin_ty_alpha

theorem Untyped.let_bin_ty_alpha_wk_elem {C: Untyped} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (elem (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (elem (var 1) (var 0))).wk (ρ.liftn 2) := let_bin_ty_alpha_wk

theorem Untyped.let_bin_ty_alpha_repr {C: Untyped} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (repr (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (repr (var 1) (var 0))).subst (σ.liftn 2) := let_bin_ty_alpha

theorem Untyped.let_bin_ty_alpha_wk_repr {C: Untyped} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (repr (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (repr (var 1) (var 0))).wk (ρ.liftn 2) := let_bin_ty_alpha_wk

theorem Untyped.let_bin_ty_alpha_wit {C: Untyped} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (wit (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (wit (var 1) (var 0))).subst (σ.liftn 2) := let_bin_ty_alpha

theorem Untyped.let_bin_ty_alpha_wk_wit {C: Untyped} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (wit (var 1) (var 0)) =
  ((C.wknth 1).alpha0 (wit (var 1) (var 0))).wk (ρ.liftn 2) := let_bin_ty_alpha_wk