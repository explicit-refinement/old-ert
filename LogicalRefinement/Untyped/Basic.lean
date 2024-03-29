import LogicalRefinement.Utils
import Mathlib.Order.MinMax

inductive AnnotSort
  | type
  | prop
  deriving DecidableEq, BEq

-- Term kinds
--TODO: consider making higher order?
inductive TermKind: List Nat -> Type
  -- Types
  | unit: TermKind []
  | pi: TermKind [0, 1] -- (pi, type, type)
  | sigma: TermKind [0, 1] -- (sigma, type, type)
  | coprod: TermKind [0, 0]
  --TODO: consider merging with (pi, prop, type)
  | assume: TermKind [0, 1]
  --TODO: consider merging with (sigma, prop, type)
  | set: TermKind [0, 1]
  --TODO: consider merging with (pi, ghost, type)
  | intersect: TermKind [0, 1]
  --TODO: consider merging with (sigma, ghost, type)
  | union: TermKind [0, 1]

  -- Propositions
  | top: TermKind []
  | bot: TermKind []
  --TODO: consider merging with (pi, prop, prop)
  | dimplies: TermKind [0, 1]
  --TODO: consider dependent and, analogous to (sigma, prop, prop)
  | dand: TermKind [0, 1]
  | or: TermKind [0, 0]
  --TODO: consider merging with (pi, type, prop) == (pi, ghost, prop)
  | forall_: TermKind [0, 1]
  --TODO: consider merging with (sigma, type, prop) == (sigma, ghost, prop)
  | exists_: TermKind [0, 1]

  -- Terms
  | nil: TermKind []
  -- Consider merging with intro/elim for (pi, type, type)
  | lam: TermKind [0, 1]
  | app: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, type, type)
  | pair: TermKind [0, 0]
  | let_pair: AnnotSort -> TermKind [0, 0, 2]
  | inj (b: Fin 2): TermKind [0]
  | case: AnnotSort -> TermKind [0, 0, 1, 1]
  -- Consider merging with intro/elim for (pi, type, prop)
  | lam_pr: TermKind [0, 1]
  | app_pr: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, type, prop)
  | elem: TermKind [0, 0]
  | let_set: AnnotSort -> TermKind [0, 0, 2]
  -- Consider merging with intro/elim for (pi, ghost, type)
  | lam_irrel: TermKind [0, 1]
  | app_irrel: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, ghost, type)
  | repr: TermKind [0, 0]
  | let_repr: AnnotSort -> TermKind [0, 0, 2]

  -- Proofs
  | triv: TermKind []
  | abort: TermKind [0]
  -- Consider merging with intro/elim for (pi, prop, prop)
  | imp: TermKind [0, 1]
  | mp: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, prop, prop)
  | dconj: TermKind [0, 0]
  | let_conj: TermKind [0, 0, 2]
  | disj (b: Fin 2): TermKind [0]
  | case_pr: TermKind [0, 0, 1, 1]
  -- Consider merging with intro/elim for
  -- (pi, ghost, prop) == (pi, type, prop)
  | general: TermKind [0, 1]
  | inst: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for
  -- (sigma, ghost, prop) == (sigma, type, prop)
  | wit: TermKind [0, 0]
  | let_wit: TermKind [0, 0, 2]

  -- Theory of equality
  | eq: TermKind [0, 0, 0]
  | refl: TermKind [0]
  | discr: TermKind [0, 0, 0]
  | unit_unique: TermKind [0]
  | cong: TermKind [0, 0, 1]
  | trans: TermKind [0, 0, 1]
  | beta: TermKind [0, 1]
  | beta_trans: TermKind [0, 0, 1]
  | beta_pr: TermKind [0, 1]
  | beta_ir: TermKind [0, 1]
  | beta_left: TermKind [0, 0, 1, 1]
  | beta_right: TermKind [0, 0, 1, 1]
  | beta_pair: TermKind [0, 0, 0, 2]
  | beta_set: TermKind [0, 0, 0, 2]
  | beta_repr: TermKind [0, 0, 0, 2]
  | eta: TermKind [0, 0]
  | irir: TermKind [0, 0, 0]
  | prir: TermKind [0, 0, 1]

  -- Natural numbers
  | nats: TermKind []
  | zero: TermKind []
  | succ: TermKind []
  | natrec: AnnotSort -> TermKind [1, 0, 0, 2]
  | beta_zero: TermKind [1, 0, 2]
  | beta_succ: TermKind [1, 0, 0, 2]

inductive Term: Type
  | var (v: Nat)

  | const (c: TermKind [])
  | unary (k: TermKind [0]) (t: Term)
  | let_bin (k: TermKind [0, 0, 2]) (P: Term) (e: Term) (e': Term)
  | let_bin_beta (k: TermKind [0, 0, 0, 2]) (P: Term) (l r: Term) (e': Term)
  | bin (k: TermKind [0, 0]) (l: Term) (r: Term)
  | abs (k: TermKind [0, 1]) (A: Term) (t: Term)
  | tri (k: TermKind [0, 0, 0]) (A: Term) (l: Term) (r: Term)
  | ir (k: TermKind [0, 0, 1]) (x: Term) (y: Term) (P: Term)
  | cases (k: TermKind [0, 0, 1, 1]) (K: Term) (d: Term) (l: Term) (r: Term)
  | nr (k: TermKind [1, 0, 0, 2]) (K: Term) (e: Term) (z: Term) (s: Term)
  | nz (k: TermKind [1, 0, 2]) (K: Term) (z: Term) (s: Term)

-- Types
abbrev Term.unit := const TermKind.unit
abbrev Term.nats := const TermKind.nats
abbrev Term.pi := abs TermKind.pi
abbrev Term.sigma := abs TermKind.sigma
abbrev Term.coprod := bin TermKind.coprod
abbrev Term.set := abs TermKind.set
abbrev Term.assume := abs TermKind.assume
abbrev Term.intersect := abs TermKind.intersect
abbrev Term.union := abs TermKind.union

-- Propositions
abbrev Term.top := const TermKind.top
abbrev Term.bot := const TermKind.bot
abbrev Term.dand := abs TermKind.dand
abbrev Term.or := bin TermKind.or
abbrev Term.dimplies := abs TermKind.dimplies
abbrev Term.forall_ := abs TermKind.forall_
abbrev Term.exists_ := abs TermKind.exists_
abbrev Term.eq := tri TermKind.eq

-- Terms
abbrev Term.nil := const TermKind.nil
abbrev Term.lam := abs TermKind.lam
abbrev Term.app := tri TermKind.app
abbrev Term.pair := bin TermKind.pair
abbrev Term.let_pair := λk => let_bin (TermKind.let_pair k)
abbrev Term.inj := λb => unary (TermKind.inj b)
abbrev Term.case := λk => cases (TermKind.case k)
abbrev Term.elem := bin TermKind.elem
abbrev Term.let_set := λk => let_bin (TermKind.let_set k)
abbrev Term.lam_pr := abs TermKind.lam_pr
abbrev Term.app_pr := tri TermKind.app_pr
abbrev Term.lam_irrel := abs TermKind.lam_irrel
abbrev Term.app_irrel := tri TermKind.app_irrel
abbrev Term.repr := bin TermKind.repr
abbrev Term.let_repr := λk => let_bin (TermKind.let_repr k)

-- Proofs
abbrev Term.triv := const TermKind.triv
abbrev Term.abort := unary TermKind.abort
abbrev Term.dconj := bin TermKind.dconj
abbrev Term.let_conj := let_bin TermKind.let_conj
abbrev Term.disj := λb => unary (TermKind.disj b)
abbrev Term.case_pr := cases TermKind.case_pr
abbrev Term.imp := abs TermKind.imp
abbrev Term.mp := tri TermKind.mp
abbrev Term.general := abs TermKind.general
abbrev Term.inst := tri TermKind.inst
abbrev Term.wit := bin TermKind.wit
abbrev Term.let_wit := let_bin TermKind.let_wit

-- Theory of equality
abbrev Term.refl := unary TermKind.refl
abbrev Term.discr := tri TermKind.discr
abbrev Term.unit_unique := unary TermKind.unit_unique
abbrev Term.cong := ir TermKind.cong
abbrev Term.trans := ir TermKind.trans
abbrev Term.beta := abs TermKind.beta
abbrev Term.beta_trans := ir TermKind.beta_trans
abbrev Term.beta_pr := abs TermKind.beta_pr
abbrev Term.beta_ir := abs TermKind.beta_ir
abbrev Term.eta := bin TermKind.eta
abbrev Term.irir := tri TermKind.irir
abbrev Term.prir := ir TermKind.prir
abbrev Term.beta_left := cases TermKind.beta_left
abbrev Term.beta_right := cases TermKind.beta_right
abbrev Term.beta_pair := let_bin_beta TermKind.beta_pair
abbrev Term.beta_set := let_bin_beta TermKind.beta_set
abbrev Term.beta_repr := let_bin_beta TermKind.beta_repr

-- Natural numbers
abbrev Term.zero := const TermKind.zero
abbrev Term.succ := const TermKind.succ
abbrev Term.natrec (k) := nr (TermKind.natrec k)
abbrev Term.beta_zero := nz TermKind.beta_zero
abbrev Term.beta_succ := nr TermKind.beta_succ

@[simp] def Term.fv: Term -> Nat
  | var v => Nat.succ v
  | const _ => 0
  | unary _ t => fv t
  | let_bin _ P e e' => Nat.max (fv P) (Nat.max (fv e) ((fv e') - 2))
  | let_bin_beta _ P l r e' => Nat.max (fv P) (Nat.max (fv l) (Nat.max (fv r) ((fv e') - 2)))
  | bin _ l r => Nat.max (fv l) (fv r)
  | abs _ A t => Nat.max (fv A) (fv t - 1)
  | tri _ A l r => Nat.max (fv A) (Nat.max (fv l) (fv r))
  | ir _ x y p => Nat.max (fv x) (Nat.max (fv y) (fv p - 1))
  | cases _ K d l r => Nat.max (fv K) (Nat.max (fv d) (Nat.max (fv l - 1) (fv r - 1)))
  | nr _ K e z s => Nat.max (fv K - 1) (Nat.max (fv e) (Nat.max (fv z) (fv s - 2)))
  | nz _ K z s => Nat.max (fv K - 1) (Nat.max (fv z) (fv s - 2))

@[simp] def Term.has_dep: Term -> Nat -> Prop
  | var v, i => v = i
  | const _, _ => False
  | unary _ t, i => has_dep t i
  | let_bin _ P e e', i =>
    has_dep P i ∨ has_dep e i ∨ has_dep e' (i + 2)
  | let_bin_beta _ P l r e', i =>
    has_dep P i ∨ has_dep l i ∨ has_dep r i ∨ has_dep e' (i + 2)
  | bin _ l r, i => has_dep l i ∨ has_dep r i
  | abs _ A t, i => has_dep A i ∨ has_dep t (i + 1)
  | tri _ A l r, i => has_dep A i ∨ has_dep l i ∨ has_dep r i
  | ir _ x y p, i => has_dep x i ∨ has_dep y i ∨ has_dep p (i + 1)
  | cases _ K d l r, i =>
    has_dep K i ∨ has_dep d i ∨ has_dep l (i + 1) ∨ has_dep r (i + 1)
  | nr _ K e z s, i =>
    has_dep K (i + 1) ∨ has_dep e i ∨ has_dep z i ∨ has_dep s (i + 2)
  | nz _ K z s, i =>
    has_dep K (i + 1) ∨ has_dep z i ∨ has_dep s (i + 2)

theorem Term.has_dep_dimplies_fv (u: Term): {i: Nat} ->
  has_dep u i -> i < fv u := by {
    induction u <;>
    simp only [has_dep, fv, lt_max_iff];
    case var v =>
      intro i H
      apply Nat.le_of_lt_succ
      rw [H]
      apply Nat.le_refl

    all_goals (
      intro i;
      repeat any_goals (apply or_imp_decompose; apply And.intro);
      all_goals (
        intro H
        try apply Nat.lt_sub_of_add_lt
        revert H
      )
      try any_goals simp
    )
    --TODO: why can't the same name be reused
    any_goals rename_i I0
    any_goals apply I0
    any_goals rename_i I1
    any_goals apply I1
    any_goals rename_i I2
    any_goals apply I2
    any_goals rename_i I3
    any_goals apply I3
  }
