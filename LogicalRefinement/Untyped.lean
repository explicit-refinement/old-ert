-- Based off https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda

import Init.Data.Nat
import LogicalRefinement.Wk
import LogicalRefinement.Utils

-- Term kinds
inductive UntypedKind: List Nat -> Type
  -- Types
  | nats: UntypedKind []
  | pi: UntypedKind [0, 1]
  | sigma: UntypedKind [0, 1]
  | coprod: UntypedKind [0, 0]
  | set: UntypedKind [0, 1]
  | assume: UntypedKind [0, 1]
  | intersect: UntypedKind [0, 1]
  | union: UntypedKind [0, 1]

  -- Propositions
  | top: UntypedKind []
  | bot: UntypedKind []
  | and: UntypedKind [0, 0]
  | or: UntypedKind [0, 0]
  | implies: UntypedKind [0, 0]
  | forall_: UntypedKind [0, 1]
  | exists_: UntypedKind [0, 1]
  | eq: UntypedKind [0, 0, 0]

  -- Terms
  | nat (n: Nat): UntypedKind []
  | lam: UntypedKind [0, 1]
  | app: UntypedKind [0, 0]
  | pair: UntypedKind [0, 0]
  | proj (b: Bool): UntypedKind [0, 0]
  | inj (b: Bool): UntypedKind [0, 0]
  | case: UntypedKind [0, 0, 0]
  | mkset: UntypedKind [0, 0]
  | letset: UntypedKind [2]
  | lam_pr: UntypedKind [0, 1]
  | app_pr: UntypedKind [0, 0]
  | lam_irrel: UntypedKind [0, 1]
  | app_irrel: UntypedKind [0, 0]
  | repr: UntypedKind [0, 0]
  | let_repr: UntypedKind [2]

  -- Proofs
  | nil: UntypedKind []
  | abort: UntypedKind [0]
  | conj: UntypedKind [0, 0]
  | comp (b: Bool): UntypedKind [0, 0]
  | disj (b: Bool): UntypedKind [0, 0]
  | case_pr: UntypedKind [0, 0, 0]
  | imp: UntypedKind [0, 0]
  | mp: UntypedKind [0, 0]
  | general: UntypedKind [0, 1]
  | inst: UntypedKind [0, 0]
  | witness: UntypedKind [0, 0]
  | let_wit: UntypedKind [2]
  | refl: UntypedKind [0]

inductive RawUntyped: Type
  | var (v: Nat)

  | const (c: UntypedKind [])
  | unary (k: UntypedKind [0]) (t: RawUntyped)
  -- TODO: let n?
  | let_bin (k: UntypedKind [2]) (e: RawUntyped)
  -- TODO: bin n? Can't, due to, of course, lack of nested inductive types...
  | bin (k: UntypedKind [0, 0]) (l: RawUntyped) (r: RawUntyped)
  -- TODO: abs n?
  | abs (k: UntypedKind [0, 1]) (A: RawUntyped) (t: RawUntyped)
  -- TODO: no cases?
  | cases (k: UntypedKind [0, 0, 0]) (d: RawUntyped) (l: RawUntyped) (r: RawUntyped)

@[simp] def RawUntyped.fv: RawUntyped -> Nat
  | var v => Nat.succ v
  | const c => 0
  | unary _ t => fv t
  | let_bin _ e => (fv e) - 2
  | bin _ l r => Nat.max (fv l) (fv r)
  | abs _ A t => Nat.max (fv A) (fv t - 1)
  | cases _ d l r => Nat.max (fv d) (Nat.max (fv l) (fv r))

@[simp] def RawUntyped.has_dep: RawUntyped -> Nat -> Prop
  | var v, i => v = i
  | const c, _ => False
  | unary _ t, i => has_dep t i
  | let_bin _ e, i => has_dep e (i + 2)
  | bin _ l r, i => has_dep l i ∨ has_dep r i
  | abs _ A t, i => has_dep A i ∨ has_dep t (i + 1)
  | cases _ d l r, i => has_dep d i ∨ has_dep l i ∨ has_dep r i

theorem RawUntyped.has_dep_implies_fv (u: RawUntyped): {i: Nat} ->
  has_dep u i -> i < fv u := by {
    induction u with
    | var v =>
      simp
      intro i H
      apply Nat.le_lt_succ
      apply Nat.le_of_eq
      rw [H]
    | const c => simp
    | unary _ t I => simp; apply I
    | let_bin _ e I =>
      intro i
      simp only [has_dep, fv]
      intro H
      let H' := I H
      exact Nat.lt_sub_lt_add H'
    | bin _ l r Il Ir =>
      intro i
      simp only [has_dep, fv, Nat.max_l_lt_split]
      intro H
      cases H with
      | inl H => exact Or.inl (Il H)
      | inr H => exact Or.inr (Ir H)
    | abs _ A t IA It => 
      intro i
      simp only [has_dep, fv, Nat.max_l_lt_split]
      intro H
      cases H with
      | inl H => exact Or.inl (IA H)
      | inr H => exact Or.inr (Nat.lt_sub_lt_add (It H))
    | cases _ d l r Id Il Ir =>
      intro i
      simp only [has_dep, fv, Nat.max_l_lt_split]
      intro H
      exact (
        match H with
        | Or.inl H => Or.inl (Id H)
        | Or.inr (Or.inl H) => Or.inr (Or.inl (Il H))
        | Or.inr (Or.inr H) => Or.inr (Or.inr (Ir H))
      )
  }

structure Untyped (n: Nat) := (val: RawUntyped) (p: RawUntyped.fv val ≤ n)

def Untyped.raw (val: RawUntyped): Untyped (RawUntyped.fv val) :=
  Untyped.mk val (Nat.le_of_eq rfl)

def Untyped.fv: Untyped n -> Fin (n + 1) 
  | Untyped.mk val p => Fin.mk (RawUntyped.fv val) (Nat.le_lt_succ p)

@[simp] def RawUntyped.wk (ρ: RawWk): RawUntyped -> RawUntyped
  | var v => var (RawWk.var ρ v)
  | const c => const c
  | unary k t => unary k (wk ρ t)
  | let_bin k e => let_bin k (wk (RawWk.liftn 2 ρ) e)
  | bin k l r => bin k (wk ρ l) (wk ρ r)
  | abs k A t => abs k (wk ρ A) (wk (RawWk.lift ρ) t)
  | cases k d l r => cases k (wk ρ d) (wk ρ l) (wk ρ r)

@[simp] def RawUntyped.wk1 (u: RawUntyped) := wk RawWk.wk1 u

@[simp] def RawUntyped.wkn (n: Nat) (u: RawUntyped) := wk (RawWk.wkn n) u

def RawUntyped.wk_bounds {u: RawUntyped}: {n m: Nat} -> {ρ: RawWk} ->
  wk_maps n m ρ -> fv u ≤ m -> fv (wk ρ u) ≤ n := by {
    induction u with
    | var v => intros _ _ ρ Hm. apply Hm
    | const => intros. apply Nat.zero_le
    | unary k t IHt => 
      intros _ _ ρ Hm
      apply IHt Hm
    | let_bin k e IHe =>
      simp only [fv, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      apply IHe
      apply wk_maps_liftn
      apply Hm
    | bin k l r IHl IHr =>
      simp only [fv, Nat.max_r_le_split]
      intros n m ρ Hm
      intro ⟨Hl, Hr⟩
      apply And.intro;
      case bin.left => apply IHl Hm Hl
      case bin.right => apply IHr Hm Hr
    | abs k A s IHA IHs =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HA, Hs⟩
      apply And.intro;
      case abs.left => apply IHA Hm HA
      case abs.right => 
        let Hm' := @wk_maps_liftn 1 n m ρ Hm
        apply IHs Hm' Hs
    | cases k d l r IHd IHl IHr => 
      simp only [fv, Nat.max_r_le_split]
      intros n m ρ Hm
      intro ⟨Hd, Hl, Hr⟩
      apply And.intro;
      case cases.left => apply IHd Hm Hd
      case cases.right =>
        apply And.intro;
        case left => apply IHl Hm Hl
        case right => apply IHr Hm Hr
  }

@[simp] def RawUntyped.wk_composes (u: RawUntyped): 
  (σ ρ: RawWk) -> wk σ (wk ρ u) = wk (RawWk.comp σ ρ) u := by {
  induction u with
  | var v => simp
  | const c => simp
  | unary k t I => simp [I]
  | let_bin k t I => simp [I]
  | bin k l r Il Ir => simp [Il, Ir]
  | abs k A t IA It => simp [IA, It] 
  | cases k d l r Id Il Ir => simp [Id, Il, Ir]
}

@[simp] def Untyped.wk (ρ: Wk n m) (u: Untyped m): Untyped n :=
  Untyped.mk (RawUntyped.wk ρ.val u.val) (RawUntyped.wk_bounds ρ.p u.p)

@[simp] def Untyped.wk_composes (σ: Wk n m) (ρ: Wk m l):
  wk σ (wk ρ u) = wk (Wk.comp σ ρ) u := by simp

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

theorem RawSubst.lift_liftn_merge (n: Nat) {σ: RawSubst}:
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
  | zero => sorry
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

@[simp]
def RawUntyped.subst (σ: RawSubst): RawUntyped -> RawUntyped
  | var v => σ v
  | const c => const c
  | unary k t => unary k (subst σ t)
  | let_bin k t => let_bin k (subst (RawSubst.liftn 2 σ) t)
  | bin k l r => bin k (subst σ l) (subst σ r)
  | abs k A t => abs k (subst σ A) (subst (RawSubst.lift σ) t)
  | cases k d l r => cases k (subst σ d) (subst σ l) (subst σ r)

theorem RawUntyped.liftn_wk {u: RawUntyped}: {σ: RawSubst} -> (n: Nat) ->
  subst (RawSubst.liftn (n + 1) σ) (wkn n u) =
  wkn n (subst (RawSubst.liftn n σ) u)
  := by {
    unfold RawWk.wk1
    induction u with
    | var v => sorry
    | const c => simp
    | unary k t I => 
      intros σ n
      simp only [wkn, wk, subst]
      simp only [wkn] at I
      rw [I]
    | let_bin k e I =>
      intros σ n
      simp only [wkn, wk, subst, RawWk.liftn_wkn_merge]
      rw [RawSubst.liftn_merge]
      simp only [wkn] at I
      rw [I]
      simp
    | bin k l r Il Ir =>
      intros σ n
      simp only [wkn, wk, subst]
      simp only [wkn] at Il
      simp only [wkn] at Ir
      rw [Il]
      rw [Ir]
    | abs k A t IA It => 
      intros σ n
      simp only [wkn, wk, subst]
      simp only [wkn] at IA
      simp only [wkn] at It
      rw [IA]
      rw [RawWk.lift_wkn_merge _ _]
      rw [RawSubst.lift_liftn_merge _]
      rw [RawSubst.lift_liftn_merge _]
      rw [It]
      exact 0 -- TODO: why?
    | cases k d l r Id Il Ir =>
      intros σ n
      simp only [wkn, wk, subst]
      simp only [wkn] at Id
      simp only [wkn] at Il
      simp only [wkn] at Ir
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
