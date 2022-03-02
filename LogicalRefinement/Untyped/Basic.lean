import LogicalRefinement.Utils

-- Term kinds
--TODO: consider making higher order?
inductive UntypedKind: List Nat -> Type
  -- Types
  | nats: UntypedKind []
  | pi: UntypedKind [0, 1] -- (pi, type, type)
  | sigma: UntypedKind [0, 1] -- (sigma, type, type)
  | coprod: UntypedKind [0, 0]
  --TODO: consider merging with (pi, prop, type)
  | assume: UntypedKind [0, 1]
  --TODO: consider merging with (sigma, prop, type)
  | set: UntypedKind [0, 1]
  --TODO: consider merging with (pi, ghost, type)
  | intersect: UntypedKind [0, 1]
  --TODO: consider merging with (sigma, ghost, type)
  | union: UntypedKind [0, 1]

  -- Propositions
  | top: UntypedKind []
  | bot: UntypedKind []
  --TODO: consider merging with (pi, prop, prop)
  | implies: UntypedKind [0, 1]
  --TODO: consider dependent and, analogous to (sigma, prop, prop)
  | and: UntypedKind [0, 0] 
  | or: UntypedKind [0, 0]
  --TODO: consider merging with (pi, type, prop) == (pi, ghost, prop)
  | forall_: UntypedKind [0, 1]
  --TODO: consider merging with (sigma, type, prop) == (sigma, ghost, prop)
  | exists_: UntypedKind [0, 1]
  | eq: UntypedKind [0, 0, 0]

  -- Terms
  | zero: UntypedKind []
  | succ: UntypedKind []
  -- Consider merging with intro/elim for (pi, type, type)
  | lam: UntypedKind [0, 1]
  | app: UntypedKind [0, 0]
  -- Consider merging with intro/elim for (sigma, type, type)
  | pair: UntypedKind [0, 0]
  | let_pair: UntypedKind [0, 2]
  | inj (b: Bool): UntypedKind [0]
  | case: UntypedKind [1, 0, 1, 1]
  | cases: UntypedKind [1]
  -- Consider merging with intro/elim for (pi, type, prop)
  | lam_pr: UntypedKind [0, 1]
  | app_pr: UntypedKind [0, 0]
  -- Consider merging with intro/elim for (sigma, type, prop)
  | elem: UntypedKind [0, 0]
  | let_set: UntypedKind [0, 2]
  -- Consider merging with intro/elim for (pi, ghost, type)
  | lam_irrel: UntypedKind [0, 1]
  | app_irrel: UntypedKind [0, 0]
  -- Consider merging with intro/elim for (sigma, ghost, type)
  | repr: UntypedKind [0, 0]
  | let_repr: UntypedKind [0, 2]

  -- Proofs
  | nil: UntypedKind []
  | abort: UntypedKind [0]
  -- Consider merging with intro/elim for (pi, prop, prop)
  | imp: UntypedKind [0, 1]
  | mp: UntypedKind [0, 0]
  -- Note: (sigma, prop, prop) is not dependent, unlike for prop!  
  | conj: UntypedKind [0, 0]
  | comp (b: Bool): UntypedKind [0]
  | disj (b: Bool): UntypedKind [0]
  | case_pr: UntypedKind [1, 0, 1, 1]
  -- Consider merging with intro/elim for 
  -- (pi, ghost, prop) == (pi, type, prop)
  | general: UntypedKind [0, 1]
  | inst: UntypedKind [0, 0]
  -- Consider merging with intro/elim for 
  -- (sigma, ghost, prop) == (sigma, type, prop)
  | wit: UntypedKind [0, 0]
  | let_wit: UntypedKind [0, 2]
  | refl: UntypedKind [0]

inductive Untyped: Type
  | var (v: Nat)

  | const (c: UntypedKind [])
  | unary (k: UntypedKind [0]) (t: Untyped)
  -- TODO: let n?
  | let_bin (k: UntypedKind [0, 2]) (e: Untyped) (e': Untyped)
  -- TODO: bin n? Can't, due to, of course, lack of nested inductive types...
  | bin (k: UntypedKind [0, 0]) (l: Untyped) (r: Untyped)
  -- TODO: abs n?
  | abs (k: UntypedKind [0, 1]) (A: Untyped) (t: Untyped)
  | tri (k: UntypedKind [0, 0, 0]) (A: Untyped) (l: Untyped) (r: Untyped)
  -- TODO: no cases?
  | cases (k: UntypedKind [1, 0, 1, 1]) (K: Untyped) (d: Untyped) (l: Untyped) (r: Untyped)

-- Types
def Untyped.nats := const UntypedKind.nats
def Untyped.pi := abs UntypedKind.pi
def Untyped.sigma := abs UntypedKind.sigma
def Untyped.coprod := bin UntypedKind.coprod
def Untyped.set := abs UntypedKind.set
def Untyped.assume := abs UntypedKind.assume
def Untyped.intersect := abs UntypedKind.intersect
def Untyped.union := abs UntypedKind.union

-- Propositions
def Untyped.top := const UntypedKind.top
def Untyped.bot := const UntypedKind.bot
def Untyped.and := bin UntypedKind.and
def Untyped.or := bin UntypedKind.or
def Untyped.implies := abs UntypedKind.implies
def Untyped.forall_ := abs UntypedKind.forall_
def Untyped.exists_ := abs UntypedKind.exists_
def Untyped.eq := tri UntypedKind.eq

-- Terms
def Untyped.zero := const UntypedKind.zero
def Untyped.succ := const UntypedKind.succ
def Untyped.lam := abs UntypedKind.lam
def Untyped.app := bin UntypedKind.app
def Untyped.pair := bin UntypedKind.pair
def Untyped.let_pair := let_bin UntypedKind.let_pair
def Untyped.inj := λb => unary (UntypedKind.inj b)
def Untyped.case := cases UntypedKind.case
def Untyped.elem := bin UntypedKind.elem
def Untyped.let_set := let_bin UntypedKind.let_set
def Untyped.lam_pr := abs UntypedKind.lam_pr
def Untyped.app_pr := bin UntypedKind.app_pr
def Untyped.lam_irrel := abs UntypedKind.lam_irrel
def Untyped.app_irrel := bin UntypedKind.app_irrel
def Untyped.repr := bin UntypedKind.repr
def Untyped.let_repr := let_bin UntypedKind.let_repr

-- Proofs
def Untyped.nil := const UntypedKind.nil
def Untyped.abort := unary UntypedKind.abort
def Untyped.conj := bin UntypedKind.conj
def Untyped.comp := λb => unary (UntypedKind.comp b)
def Untyped.disj := λb => unary (UntypedKind.disj b)
def Untyped.case_pr := cases UntypedKind.case_pr
def Untyped.imp := abs UntypedKind.imp
def Untyped.mp := bin UntypedKind.mp
def Untyped.general := abs UntypedKind.general
def Untyped.inst := bin UntypedKind.inst
def Untyped.wit := bin UntypedKind.wit
def Untyped.let_wit := let_bin UntypedKind.let_wit
def Untyped.refl := unary UntypedKind.refl

@[simp] def Untyped.fv: Untyped -> Nat
  | var v => Nat.succ v
  | const c => 0
  | unary _ t => fv t
  | let_bin _ e e' => Nat.max (fv e) ((fv e') - 2)
  | bin _ l r => Nat.max (fv l) (fv r)
  | abs _ A t => Nat.max (fv A) (fv t - 1)
  | tri _ A l r => Nat.max (fv A) (Nat.max (fv l) (fv r))
  | cases _ K d l r => Nat.max (fv K - 1) (Nat.max (fv d) (Nat.max (fv l - 1) (fv r - 1)))

@[simp] def Untyped.has_dep: Untyped -> Nat -> Prop
  | var v, i => v = i
  | const c, _ => False
  | unary _ t, i => has_dep t i
  | let_bin _ e e', i => has_dep e i ∨ has_dep e' (i + 2)
  | bin _ l r, i => has_dep l i ∨ has_dep r i
  | abs _ A t, i => has_dep A i ∨ has_dep t (i + 1)
  | tri _ A l r, i => has_dep A i ∨ has_dep l i ∨ has_dep r i
  | cases _ K d l r, i => 
    has_dep K (i + 1) ∨ has_dep d i ∨ has_dep l (i + 1) ∨ has_dep r (i + 1)

theorem Untyped.has_dep_implies_fv (u: Untyped): {i: Nat} ->
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