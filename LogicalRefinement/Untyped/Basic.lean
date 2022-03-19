import LogicalRefinement.Utils

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
  | eq: TermKind [0, 0, 0]

  -- Terms
  | nil: TermKind []
  -- Consider merging with intro/elim for (pi, type, type)
  | lam: TermKind [0, 1]
  | app: TermKind [0, 0, 0]
  -- Consider merging with intro/elim for (sigma, type, type)
  | pair: TermKind [0, 0]
  | let_pair: TermKind [0, 2]
  | inj (b: Bool): TermKind [0]
  | case: TermKind [0, 0, 1, 1]
  -- Consider merging with intro/elim for (pi, type, prop)
  | lam_pr: TermKind [0, 1]
  | app_pr: TermKind [0, 0]
  -- Consider merging with intro/elim for (sigma, type, prop)
  | elem: TermKind [0, 0]
  | let_set: TermKind [0, 2]
  -- Consider merging with intro/elim for (pi, ghost, type)
  | lam_irrel: TermKind [0, 1]
  | app_irrel: TermKind [0, 0]
  -- Consider merging with intro/elim for (sigma, ghost, type)
  | repr: TermKind [0, 0]
  | let_repr: TermKind [0, 2]

  -- Proofs
  | triv: TermKind []
  | abort: TermKind [0]
  -- Consider merging with intro/elim for (pi, prop, prop)
  | imp: TermKind [0, 1]
  | mp: TermKind [0, 0]
  -- Note: (sigma, prop, prop) is not dependent, unlike for prop!  
  | dconj: TermKind [0, 0]
  | comp (b: Bool): TermKind [0]
  | disj (b: Bool): TermKind [0]
  | case_pr: TermKind [0, 0, 1, 1]
  -- Consider merging with intro/elim for 
  -- (pi, ghost, prop) == (pi, type, prop)
  | general: TermKind [0, 1]
  | inst: TermKind [0, 0]
  -- Consider merging with intro/elim for 
  -- (sigma, ghost, prop) == (sigma, type, prop)
  | wit: TermKind [0, 0]
  | let_wit: TermKind [0, 2]

  -- Theory of equality
  | refl: TermKind [0]
  | sym: TermKind [0]
  | trans: TermKind [0]
  | cong: TermKind [0, 1]
  | beta: TermKind [0, 1]
  | eta: TermKind [0, 0]
  | irir: TermKind [0, 0, 0]
  | prir: TermKind [0, 0, 0]

  -- Natural numbers
  | nats: TermKind []
  | zero: TermKind []
  | succ: TermKind []

inductive Term: Type
  | var (v: Nat)

  | const (c: TermKind [])
  | unary (k: TermKind [0]) (t: Term)
  -- TODO: let n?
  | let_bin (k: TermKind [0, 2]) (e: Term) (e': Term)
  -- TODO: bin n? Can't, due to, of course, lack of nested inductive types...
  | bin (k: TermKind [0, 0]) (l: Term) (r: Term)
  -- TODO: abs n?
  | abs (k: TermKind [0, 1]) (A: Term) (t: Term)
  | tri (k: TermKind [0, 0, 0]) (A: Term) (l: Term) (r: Term)
  -- TODO: no cases?
  | cases (k: TermKind [0, 0, 1, 1]) (K: Term) (d: Term) (l: Term) (r: Term)
  | natrec (K: Term) (e: Term) (z: Term) (s: Term)

-- Types
def Term.unit := const TermKind.unit
def Term.nats := const TermKind.nats
def Term.pi := abs TermKind.pi
def Term.sigma := abs TermKind.sigma
def Term.coprod := bin TermKind.coprod
def Term.set := abs TermKind.set
def Term.assume := abs TermKind.assume
def Term.intersect := abs TermKind.intersect
def Term.union := abs TermKind.union

-- Propositions
def Term.top := const TermKind.top
def Term.bot := const TermKind.bot
def Term.dand := abs TermKind.dand
def Term.or := bin TermKind.or
def Term.dimplies := abs TermKind.dimplies
def Term.forall_ := abs TermKind.forall_
def Term.exists_ := abs TermKind.exists_
def Term.eq := tri TermKind.eq

-- Terms
def Term.nil := const TermKind.nil
def Term.lam := abs TermKind.lam
def Term.app := tri TermKind.app
def Term.pair := bin TermKind.pair
def Term.let_pair := let_bin TermKind.let_pair
def Term.inj := λb => unary (TermKind.inj b)
def Term.case := cases TermKind.case
def Term.elem := bin TermKind.elem
def Term.let_set := let_bin TermKind.let_set
def Term.lam_pr := abs TermKind.lam_pr
def Term.app_pr := bin TermKind.app_pr
def Term.lam_irrel := abs TermKind.lam_irrel
def Term.app_irrel := bin TermKind.app_irrel
def Term.repr := bin TermKind.repr
def Term.let_repr := let_bin TermKind.let_repr

-- Proofs
def Term.triv := const TermKind.triv
def Term.abort := unary TermKind.abort
def Term.dconj := bin TermKind.dconj
def Term.comp := λb => unary (TermKind.comp b)
def Term.disj := λb => unary (TermKind.disj b)
def Term.case_pr := cases TermKind.case_pr
def Term.imp := abs TermKind.imp
def Term.mp := bin TermKind.mp
def Term.general := abs TermKind.general
def Term.inst := bin TermKind.inst
def Term.wit := bin TermKind.wit
def Term.let_wit := let_bin TermKind.let_wit

-- Theory of equality
def Term.refl := unary TermKind.refl
def Term.sym := unary TermKind.sym
def Term.trans := unary TermKind.trans
def Term.cong := abs TermKind.cong
def Term.beta := abs TermKind.beta
def Term.eta := bin TermKind.eta
def Term.irir := tri TermKind.irir
def Term.prir := tri TermKind.prir

-- Natural numbers
def Term.zero := const TermKind.zero
def Term.succ := const TermKind.succ

@[simp] def Term.fv: Term -> Nat
  | var v => Nat.succ v
  | const c => 0
  | unary _ t => fv t
  | let_bin _ e e' => Nat.max (fv e) ((fv e') - 2)
  | bin _ l r => Nat.max (fv l) (fv r)
  | abs _ A t => Nat.max (fv A) (fv t - 1)
  | tri _ A l r => Nat.max (fv A) (Nat.max (fv l) (fv r))
  | cases _ K d l r => Nat.max (fv K) (Nat.max (fv d) (Nat.max (fv l - 1) (fv r - 1)))
  | natrec K e z s => Nat.max (fv K - 1) (Nat.max (fv e) (Nat.max (fv z) (fv s - 2)))

@[simp] def Term.has_dep: Term -> Nat -> Prop
  | var v, i => v = i
  | const c, _ => False
  | unary _ t, i => has_dep t i
  | let_bin _ e e', i => has_dep e i ∨ has_dep e' (i + 2)
  | bin _ l r, i => has_dep l i ∨ has_dep r i
  | abs _ A t, i => has_dep A i ∨ has_dep t (i + 1)
  | tri _ A l r, i => has_dep A i ∨ has_dep l i ∨ has_dep r i
  | cases _ K d l r, i => 
    has_dep K i ∨ has_dep d i ∨ has_dep l (i + 1) ∨ has_dep r (i + 1)
  | natrec K e z s, i =>
    has_dep K (i + 1) ∨ has_dep e i ∨ has_dep z i ∨ has_dep s (i + 2)

theorem Term.has_dep_dimplies_fv (u: Term): {i: Nat} ->
  has_dep u i -> i < fv u := by {
    induction u <;> 
    simp only [has_dep, fv, Nat.max_l_lt_split];
    case var v =>
      simp
      intro i H
      apply Nat.le_lt_succ
      apply Nat.le_of_eq
      rw [H]

    all_goals (
      intro i;
      repeat any_goals (apply or_imp_decompose; apply And.intro);
      all_goals (
        intro H
        try apply Nat.lt_sub_lt_add
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