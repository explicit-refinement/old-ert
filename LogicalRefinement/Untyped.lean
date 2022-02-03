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

theorem RawUntyped.wk1_no_zero_dep (u: RawUntyped): ¬has_dep (wk1 u) 0 := by {
  induction u with
  | var v =>
    simp only [has_dep, wk1, RawWk.var]
    apply Nat.succ_ne_zero
  | const c => simp
  | _ => sorry
}

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
def RawSubst.liftn (σ: RawSubst): (l: Nat) -> RawSubst
  | 0 => σ
  | Nat.succ l => lift (liftn σ l)

@[simp]
def RawUntyped.subst (σ: RawSubst): RawUntyped -> RawUntyped
  | var v => σ v
  | const c => const c
  | unary k t => unary k (subst σ t)
  | let_bin k t => let_bin k (subst (RawSubst.liftn σ 2) t)
  | bin k l r => bin k (subst σ l) (subst σ r)
  | abs k A t => abs k (subst σ A) (subst (RawSubst.lift σ) t)
  | cases k d l r => cases k (subst σ d) (subst σ l) (subst σ r)

def RawSubst.comp (σ ρ: RawSubst): RawSubst
  | v => RawUntyped.subst σ (ρ v)

@[simp] theorem RawSubst.lift_comp {ρ σ: RawSubst}: 
  comp (lift ρ) (lift σ) = lift (comp ρ σ) := by {
    funext v;
    cases v with
    | zero => simp [comp]
    | succ v => sorry
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
