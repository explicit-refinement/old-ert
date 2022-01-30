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

def RawUntyped.fv: RawUntyped -> Nat
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