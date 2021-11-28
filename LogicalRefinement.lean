-- Based off https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda

import Init.Data.Nat

--TODO: factor out generators, using the trick from logrel-mltt... or just write a tactic?

inductive GenTs (A: Nat -> Type): Nat -> List Nat -> Type where
  | nil: GenTs A n []
  | cons (t: A (h + n)) (ts: GenTs A n l): GenTs A n (h :: l)

--TODO: generated ts lifted mapper... hmm... termsize termination?
-- Think about positive termination checking for `isotope`, too...

inductive Kind: List Nat -> Type 0 where
  -- Types
  | nat: Kind []
  | pi: Kind [0, 1]
  | sigma: Kind [0, 1]
  | coprod: Kind [0, 0]
  | set: Kind [0, 1]
  | assume: Kind [0, 0]
  | intersect: Kind [0, 0]
  | union: Kind [0, 1]

  -- Propositions
  | top: Kind []
  | bot: Kind []
  | and: Kind [0, 0]
  | or: Kind [0, 0]
  | implies: Kind [0, 0]
  | forall_: Kind [0, 1]
  | exists_: Kind [0, 1]
  | eq: Kind [0, 0, 0]

  -- Terms
  | lam: Kind [0, 1]
  | app: Kind [0, 0]
  | pair: Kind [0, 0]
  | proj: Bool -> Kind [0]
  | inj: Bool -> Kind [0]
  | case: Kind [0, 0, 0]
  | mkset: Kind [0, 0]
  | letset: Kind [2]
  | lam_pr: Kind [0, 1]
  | app_pr: Kind [0, 0] --TODO: fuse with just `app`? Nah, because different hypotheses, right? (see `app_irrel`)
  | lam_irrel: Kind [0, 1]
  | app_irrel: Kind [0, 0]
  | repr: Kind [0, 0]
  | let_repr: Kind [2]

  -- Proofs
  | nil: Kind []
  | abort: Kind [0]
  | conj: Kind [0, 0]
  | comp: Bool -> Kind [0]
  | disj: Bool -> Kind [0]
  | case_pr: Kind [0, 0, 0]
  | imp: Kind [0, 1]
  | mp: Kind [0, 0]
  | general: Kind [0, 1]
  | inst: Kind [0, 0]
  | witness: Kind [0, 0]
  | let_wit: Kind [2]
  | refl: Kind [0]
  --TODO: equality axioms... could have an interesting case here for using metavariable bindings...

inductive Untyped: Nat -> Type 0 where
  | var (m: Fin n): Untyped n
  | gen: Kind l -> GenTs Untyped n l -> Untyped n

inductive Wk: Nat -> Nat -> Type 0 where
  | id: Wk n n
  | step: Wk m n -> Wk (Nat.succ m) n
  | lift: Wk m n -> Wk (Nat.succ m) (Nat.succ n)

private def wk_liftn: (l: Nat) -> Wk m n -> Wk (m + l) (n + l)
  | 0, ρ => ρ
  | Nat.succ n, ρ => Wk.lift (wk_liftn n ρ)

def Wk.liftn: (l: Nat) -> Wk m n -> Wk (m + l) (n + l) := wk_liftn

private def wk_compose: Wk n m -> Wk m l -> Wk n l
  | Wk.id, ρ => ρ
  | Wk.step ρ, ρ' => Wk.step (wk_compose ρ ρ')
  | Wk.lift ρ, Wk.id => Wk.lift ρ
  | Wk.lift ρ, Wk.step ρ' => Wk.step (wk_compose ρ ρ')
  | Wk.lift ρ, Wk.lift ρ' => Wk.lift (wk_compose ρ ρ')

def Wk.compose: Wk n m -> Wk m l -> Wk n l := wk_compose

infixl:30 " ⋅ " => wk_compose

--TODO: instantiate weakening to have a composition typeclass?

def Fin.succ: Fin n -> Fin (Nat.succ n)
  | Fin.mk m p => Fin.mk (Nat.succ m) (Nat.lt_succ_of_le p)

def Fin.zero: Fin (Nat.succ n) := Fin.mk 0 (Nat.zero_lt_of_lt (Nat.lt_succ_self _))

def wkVar: Wk n m -> Fin m -> Fin n
  | Wk.id, v => v
  | Wk.step ρ, v => Fin.succ (wkVar ρ v)
  | Wk.lift ρ, Fin.mk 0 p => Fin.zero
  | Wk.lift ρ, Fin.mk (Nat.succ n) p => Fin.succ (wkVar ρ (Fin.mk n (Nat.lt_of_succ_lt_succ p)))

def wk (ρ: Wk n m): Untyped m -> Untyped n
  | Untyped.var m => Untyped.var (wkVar ρ m)
  | Untyped.gen _ _ => sorry


inductive Hypothesis (n: Nat) where
  | comp (A: Untyped n)
  | refine (A: Untyped n)
  | logic (φ: Untyped n)

inductive Con: Nat -> Type where
  | ε: Con 0
  | cons (H: Hypothesis n) (c: Con n): Con (n + 1)

def wk1: Wk (n + 1) n := Wk.step Wk.id

def Subst (m: Nat) (n: Nat): Type 0 := Fin n -> Untyped m

def head (σ: Subst m (Nat.succ n)): Untyped m := σ Fin.zero

def tail (σ: Subst m (Nat.succ n)): Subst m n :=  λv => σ (Fin.succ v)

def idSubst: Subst n n := Untyped.var

def wk1Subst (σ: Subst m n): Subst (m + 1) n := λ x => wk wk1 (σ x)

def Subst.lift (σ: Subst m n): Subst (m + 1) (n + 1)
  | Fin.mk 0 p => Untyped.var Fin.zero
  | Fin.mk (Nat.succ n) p => wk1Subst σ (Fin.mk n (Nat.lt_of_succ_lt_succ p))

private def liftSubstn: (l: Nat) -> Subst m n -> Subst (m + l) (n + l)
  | 0, σ => σ
  | Nat.succ n, σ => Subst.lift (liftSubstn n σ)

def Subst.liftn: (l: Nat) -> Subst m n -> Subst (m + l) (n + l) := liftSubstn

def toSubst (ρ: Wk m n): Subst m n := λv => Untyped.var (wkVar ρ v)

--TODO: instantiate coercions from substitutions to weakenings?

def consSubst (σ: Subst m n) (t: Untyped n): Subst m (n + 1) := sorry

def sgSubst (t: Untyped n): Subst n (n + 1) := sorry

def subst (σ: Subst m n): Untyped n -> Untyped m
  | Untyped.var v => σ v
  | Untyped.gen _ _ => sorry

def Subst.compose (σ: Subst l m) (τ: Subst m n): Subst l n :=
  λv => subst σ (τ v)