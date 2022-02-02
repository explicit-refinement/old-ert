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
      simp only [fv, Nat.max_le_split]
      intros n m ρ Hm
      intro ⟨Hl, Hr⟩
      apply And.intro;
      case bin.left => apply IHl Hm Hl
      case bin.right => apply IHr Hm Hr
    | abs k A s IHA IHs =>
      simp only [fv, Nat.max_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HA, Hs⟩
      apply And.intro;
      case abs.left => apply IHA Hm HA
      case abs.right => 
        let Hm' := @wk_maps_liftn 1 n m ρ Hm
        apply IHs Hm' Hs
    | cases k d l r IHd IHl IHr => 
      simp only [fv, Nat.max_le_split]
      intros n m ρ Hm
      intro ⟨Hd, Hl, Hr⟩
      apply And.intro;
      case cases.left => apply IHd Hm Hd
      case cases.right =>
        apply And.intro;
        case left => apply IHl Hm Hl
        case right => apply IHr Hm Hr
  }

@[simp] def RawUntyped.wk_composes (ρ: RawWk) (σ: RawWk) (u: RawUntyped): 
  wk σ (wk ρ u) = wk (RawWk.comp σ ρ) u := by {
  induction u with
  | var v => simp
  | const c => rfl
  | unary k t I =>
    simp
    apply I
  | let_bin k t I =>
    simp
    sorry
  | bin k l r Il Ir =>
    simp
    exact (And.intro Il Ir)
  | abs k A t =>
    simp
    sorry
  | cases k d l r Id Il Ir =>
    simp
    exact ⟨Id, Il, Ir⟩
}

@[simp] def Untyped.wk (ρ: Wk n m) (u: Untyped m): Untyped n :=
  Untyped.mk (RawUntyped.wk ρ.val u.val) (RawUntyped.wk_bounds ρ.p u.p)