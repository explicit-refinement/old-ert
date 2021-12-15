-- Based off https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda

import Init.Data.Nat
import LogicalRefinement.Wk

inductive UntypedKind: Type where

  -- Types
  | nats
  | pi
  | sigma
  | coprod
  | set
  | assume
  | intersect
  | union

  -- Propositions
  | top
  | bot
  | and
  | or
  | implies
  | forall_
  | exists_
  | eq

  -- Terms
  | nat (n: Nat)
  | lam
  | app
  | pair
  | proj (b: Bool)
  | inj (b: Bool)
  | case
  | mkset
  | letset
  | lam_pr
  | app_pr
  | lam_irrel
  | app_irrel
  | repr
  | let_repr

  -- Proofs
  | nil
  | abort
  | conj
  | comp (b: Bool)
  | disj (b: Bool)
  | case_pr
  | imp
  | mp
  | general
  | inst
  | witness
  | let_wit
  | refl

inductive RawUntyped: Type where

  -- Variables
  | var (n: Nat)

  -- Base terms

  -- Types
  | nats
  | pi (A: RawUntyped) (B: RawUntyped)
  | sigma (A: RawUntyped) (B: RawUntyped)
  | coprod (A: RawUntyped) (B: RawUntyped)
  | set (A: RawUntyped) (φ: RawUntyped)
  | assume (φ: RawUntyped) (A: RawUntyped)
  | intersect (A: RawUntyped) (B: RawUntyped)
  | union (A: RawUntyped) (B: RawUntyped)

  -- Propositions
  | top
  | bot
  | and (φ: RawUntyped) (ψ: RawUntyped)
  | or (φ: RawUntyped) (ψ: RawUntyped)
  | implies (φ: RawUntyped) (ψ: RawUntyped)
  | forall_ (A: RawUntyped) (φ: RawUntyped)
  | exists_ (A: RawUntyped) (φ: RawUntyped)
  | eq (A: RawUntyped) (e: RawUntyped) (e': RawUntyped)

  -- Terms
  | nat (n: Nat)
  | lam (A: RawUntyped) (e: RawUntyped)
  | app (l: RawUntyped) (r: RawUntyped)
  | pair (l: RawUntyped) (r: RawUntyped)
  | proj (b: Bool) (e: RawUntyped)
  | inj (b: Bool) (e: RawUntyped)
  | case (e: RawUntyped) (l: RawUntyped) (r: RawUntyped)
  | mkset (e: RawUntyped) (p: RawUntyped)
  | letset (e: RawUntyped)
  | lam_pr (φ: RawUntyped) (e: RawUntyped)
  | app_pr (e: RawUntyped) (p: RawUntyped)
  | lam_irrel (A: RawUntyped) (e: RawUntyped)
  | app_irrel (l: RawUntyped) (r: RawUntyped)
  | repr (l: RawUntyped) (r: RawUntyped)
  | let_repr (e: RawUntyped)

  -- Proofs
  | nil
  | abort (p: RawUntyped)
  | conj (l: RawUntyped) (r: RawUntyped)
  | comp (b: Bool) (p: RawUntyped)
  | disj (b: Bool) (p: RawUntyped)
  | case_pr (p: RawUntyped) (l: RawUntyped) (r: RawUntyped)
  | imp (φ: RawUntyped) (p: RawUntyped)
  | mp (l: RawUntyped) (r: RawUntyped)
  | general (A: RawUntyped) (p: RawUntyped)
  | inst (p: RawUntyped) (e: RawUntyped)
  | witness (e: RawUntyped) (p: RawUntyped)
  | let_wit (p: RawUntyped)
  | refl (e: RawUntyped)

notation "genRecRawUntyped" u "=>" var "," r => match u with
  | RawUntyped.var v => var v

  | RawUntyped.nats => r UntypedKind.nats
  | RawUntyped.pi A B => r UntypedKind.pi, 0, A, 1, B
  | RawUntyped.sigma A B => r UntypedKind.sigma, 0, A, 1, B
  | RawUntyped.coprod A B => r UntypedKind.coprod, 0, A, 0, B
  | RawUntyped.set A φ => r UntypedKind.set, 0, A, 1, φ
  | RawUntyped.assume φ A => r UntypedKind.assume, 0, φ, 0, A
  | RawUntyped.intersect A B => r UntypedKind.intersect, 0, A, 1, B
  | RawUntyped.union A B => r UntypedKind.union, 0, A, 1, B

  | RawUntyped.top φ ψ => r UntypedKind.top
  | RawUntyped.bot φ ψ => r UntypedKind.bot
  | RawUntyped.and φ ψ => r UntypedKind.and, 0, φ, 0, ψ
  | RawUntyped.or φ ψ => r UntypedKind.or, 0, φ, 0, ψ
  | RawUntyped.implies φ Ψ => r UntypedKind.implies, 0, φ, 0, ψ
  | RawUntyped.forall_ A φ => r UntypedKind.forall_, 0, A, 1, φ
  | RawUntyped.exists_ A φ => r UntypedKind.exists_, 0, A, 1, φ
  | RawUntyped.eq A e e' => r UntypedKind.exists, 0, A, 0, e, 0, e'
  
  | RawUntyped.nat n => r (UntypedKind.nat n)
  | RawUntyped.lam A e => r UntypedKind.lam, 0, A, 1, e
  | RawUntyped.app l r => r UntypedKind.app, 0, l, 0, r
  | RawUntyped.pair l r => r UntypedKind.pair, 0, l, 0, r
  | RawUntyped.proj b e => r (UntypedKind.proj b), 0, e
  | RawUntyped.inj b e => r (UntypedKind.inj b), 0, e
  | RawUntyped.case e l r => r (UntypedKind.case), 0, e, 0, l, 0, r
  | RawUntyped.mkset e p => r (UntypedKind.mkset), 0, e, 1, p
  | RawUntyped.letset e => r (UntypedKind.letset), 2, e
  | RawUntyped.lam_pr φ e => r (UntypedKind.lam_pr), 0, φ, 1, e
  | RawUntyped.app_pr e p => r (UntypedKind.app_pr), 0, e, 0, p
  | RawUntyped.lam_irrel A e => r (UntypedKind.lam_irrel), 0, A, 1, e
  | RawUntyped.app_irrel l r => r (UntypedKind.app_irrel), 0, l, 0, r
  | RawUntyped.repr l r => r (UntypedKind.repr), 0, l, 0, r
  | RawUntyped.let_repr e => r (UntypedKind.let_repr), 2, e

  | RawUntyped.nil => r (UntypedKind.nil)
  | RawUntyped.abort p => r (UntypedKind.abort), 0, p
  | RawUntyped.conj l r => r (UntypedKind.conj), 0, l, 0, r
  | RawUntyped.comp b p => r (UntypedKind.comp b), 0, p
  | RawUntyped.disj b p => r (UntypedKind.disj b), 0, p
  | RawUntyped.case_pr p l r => r (UntypedKind.case_pr), 0, p, 0, l, 0, r
  | RawUntyped.imp φ p => r (UntypedKind.imp), φ, p
  | RawUntyped.mp l r => r (UntypedKind.mp), 0, l, 0, r
  | RawUntyped.general A p => r (UntypedKind.general), 0, A, 1, p
  | RawUntyped.inst p e => r (UntypedKind.inst), 0, p, 0, e
  | RawUntyped.witness e p => r (UntypedKind.witness), 0, e, 0, p
  | RawUntyped.let_wit p => r (UntypedKind.let_wit), 2, p
  | RawUntyped.refl e => r (UntypedKind.refl), 0, e

