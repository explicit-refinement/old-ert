import LogicalRefinement.Utils

-- Term kinds
inductive UntypedKind: List Nat -> Type
  -- Types
  | nats: UntypedKind []
  | pi: UntypedKind [0, 1]
  | sigma: UntypedKind [0, 1]
  | coprod: UntypedKind [0, 0]
  | set: UntypedKind [0, 1]
  | assume: UntypedKind [0, 0]
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
  | eq: UntypedKind [1, 0, 0, 0]

  -- Terms
  | nat (n: Nat): UntypedKind []
  | lam: UntypedKind [0, 1]
  | app: UntypedKind [0, 0]
  | pair: UntypedKind [0, 0]
  | proj (b: Bool): UntypedKind [0]
  | inj (b: Bool): UntypedKind [0]
  | case: UntypedKind [1, 0, 0, 0]
  | elem: UntypedKind [0, 0]
  | let_set: UntypedKind [2]
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
  | comp (b: Bool): UntypedKind [0]
  | disj (b: Bool): UntypedKind [0]
  | case_pr: UntypedKind [1, 0, 0, 0]
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
  | cases (k: UntypedKind [1, 0, 0, 0]) (K: RawUntyped) (d: RawUntyped) (l: RawUntyped) (r: RawUntyped)

-- Types
def RawUntyped.nats := const UntypedKind.nats
def RawUntyped.pi := abs UntypedKind.pi
def RawUntyped.sigma := abs UntypedKind.sigma
def RawUntyped.coprod := bin UntypedKind.coprod
def RawUntyped.set := abs UntypedKind.set
def RawUntyped.assume := bin UntypedKind.assume
def RawUntyped.intersect := abs UntypedKind.intersect
def RawUntyped.union := abs UntypedKind.union

-- Propositions
def RawUntyped.top := const UntypedKind.top
def RawUntyped.bot := const UntypedKind.bot
def RawUntyped.and := bin UntypedKind.and
def RawUntyped.or := bin UntypedKind.or
def RawUntyped.implies := bin UntypedKind.implies
def RawUntyped.forall_ := abs UntypedKind.forall_
def RawUntyped.exists_ := abs UntypedKind.exists_
def RawUntyped.eq := cases UntypedKind.eq

-- Terms
def RawUntyped.nat := λn => const (UntypedKind.nat n)
def RawUntyped.lam := abs UntypedKind.lam
def RawUntyped.app := bin UntypedKind.app
def RawUntyped.pair := bin UntypedKind.pair
def RawUntyped.proj := λb => unary (UntypedKind.proj b)
def RawUntyped.inj := λb => unary (UntypedKind.inj b)
def RawUntyped.case := cases UntypedKind.case
def RawUntyped.elem := bin UntypedKind.elem
def RawUntyped.let_set := let_bin UntypedKind.let_set
def RawUntyped.lam_pr := abs UntypedKind.lam_pr
def RawUntyped.app_pr := bin UntypedKind.app_pr
def RawUntyped.lam_irrel := abs UntypedKind.lam_irrel
def RawUntyped.app_irrel := bin UntypedKind.app_irrel
def RawUntyped.repr := bin UntypedKind.repr
def RawUntyped.let_repr := let_bin UntypedKind.let_repr

-- Proofs
def RawUntyped.nil := const UntypedKind.nil
def RawUntyped.abort := unary UntypedKind.abort
def RawUntyped.conj := bin UntypedKind.conj
def RawUntyped.comp := λb => unary (UntypedKind.comp b)
def RawUntyped.disj := λb => unary (UntypedKind.disj b)
def RawUntyped.case_pr := cases UntypedKind.case_pr
def RawUntyped.imp := bin UntypedKind.imp
def RawUntyped.mp := bin UntypedKind.mp
def RawUntyped.general := abs UntypedKind.general
def RawUntyped.inst := bin UntypedKind.inst
def RawUntyped.witness := bin UntypedKind.witness
def RawUntyped.let_wit := let_bin UntypedKind.let_wit
def RawUntyped.refl := unary UntypedKind.refl

@[simp] def RawUntyped.fv: RawUntyped -> Nat
  | var v => Nat.succ v
  | const c => 0
  | unary _ t => fv t
  | let_bin _ e => (fv e) - 2
  | bin _ l r => Nat.max (fv l) (fv r)
  | abs _ A t => Nat.max (fv A) (fv t - 1)
  | cases _ K d l r => Nat.max (fv K - 1) (Nat.max (fv d) (Nat.max (fv l) (fv r)))

@[simp] def RawUntyped.has_dep: RawUntyped -> Nat -> Prop
  | var v, i => v = i
  | const c, _ => False
  | unary _ t, i => has_dep t i
  | let_bin _ e, i => has_dep e (i + 2)
  | bin _ l r, i => has_dep l i ∨ has_dep r i
  | abs _ A t, i => has_dep A i ∨ has_dep t (i + 1)
  | cases _ K d l r, i => has_dep K (i + 1) ∨ has_dep d i ∨ has_dep l i ∨ has_dep r i

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
    | cases _ K d l r IK Id Il Ir =>
      intro i
      simp only [has_dep, fv, Nat.max_l_lt_split]
      intro H
      cases H with
      | inl H => exact Or.inl (Nat.lt_sub_lt_add (IK H))
      | inr H => apply Or.inr; exact (
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

-- Constructors
def Untyped.var (v: Nat): Untyped (Nat.succ v) :=
  Untyped.mk (RawUntyped.var v) (Nat.lt_succ_self _)
def Untyped.const (c: UntypedKind []): Untyped n :=
  Untyped.mk (RawUntyped.const c) (Nat.zero_le _)
def Untyped.unary (c: UntypedKind [0]): Untyped n -> Untyped n
  | u => Untyped.mk (RawUntyped.unary c u.val) u.p
def Untyped.let_bin (c: UntypedKind [2]): Untyped (n + 2) -> Untyped n
  | u => Untyped.mk (RawUntyped.let_bin c u.val) (by {
    simp only [RawUntyped.fv, Nat.le_sub_is_le_add]
    exact u.p
  })
def Untyped.bin (c: UntypedKind [0, 0]): 
  Untyped n -> Untyped n -> Untyped n
  | l, r => Untyped.mk (RawUntyped.bin c l.val r.val) (by {
    simp only [RawUntyped.fv, Nat.max_r_le_split]
    exact ⟨l.p, r.p⟩
  })
def Untyped.abs (c: UntypedKind [0, 1]): 
  Untyped n -> Untyped (n + 1) -> Untyped n
  | l, r => Untyped.mk (RawUntyped.abs c l.val r.val) (by {
    simp only [RawUntyped.fv, Nat.max_r_le_split]
    apply And.intro;
    case left => exact l.p
    case right => 
      simp only [RawUntyped.fv, Nat.le_sub_is_le_add]
      exact r.p
  })
def Untyped.cases (c: UntypedKind [1, 0, 0, 0]):
  Untyped (n + 1) -> Untyped n -> Untyped n -> Untyped n -> Untyped n
  | K, d, l, r =>
    Untyped.mk (RawUntyped.cases c K.val d.val l.val r.val) (by {
      simp only [RawUntyped.fv, Nat.max_r_le_split]
      apply And.intro;
      case left => simp only [Nat.le_sub_is_le_add]; apply K.p
      case right => exact ⟨d.p, l.p, r.p⟩
    })

-- Types
def Untyped.nats: Untyped n := const UntypedKind.nats
def Untyped.pi: Untyped n -> Untyped (n + 1) -> Untyped n := 
  abs UntypedKind.pi
def Untyped.sigma: Untyped n -> Untyped (n + 1) -> Untyped n := 
  abs UntypedKind.sigma
def Untyped.coprod: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.coprod
def Untyped.set: Untyped n -> Untyped (n + 1) -> Untyped n 
  := abs UntypedKind.set
def Untyped.assume: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.assume
def Untyped.intersect: Untyped n -> Untyped (n + 1) -> Untyped n 
  := abs UntypedKind.intersect
def Untyped.union: Untyped n -> Untyped (n + 1) -> Untyped n 
  := abs UntypedKind.union

-- Propositions
def Untyped.top: Untyped n := const UntypedKind.top
def Untyped.bot: Untyped n := const UntypedKind.bot
def Untyped.and: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.and
def Untyped.or: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.or
def Untyped.implies: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.implies
def Untyped.forall_: Untyped n -> Untyped (n + 1) -> Untyped n
  := abs UntypedKind.forall_
def Untyped.exists_: Untyped n -> Untyped (n + 1) -> Untyped n 
  := abs UntypedKind.exists_
def Untyped.eq: Untyped (n + 1) -> Untyped n -> Untyped n -> Untyped n -> Untyped n
  := cases UntypedKind.eq

-- Terms
def Untyped.nat (m: Nat): Untyped n := const (UntypedKind.nat m)
def Untyped.lam: Untyped n -> Untyped (n + 1) -> Untyped n
   := abs UntypedKind.lam
def Untyped.app: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.app
def Untyped.pair: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.pair
def Untyped.proj (b: Bool): Untyped n -> Untyped n 
  := unary (UntypedKind.proj b)
def Untyped.inj (b: Bool): Untyped n -> Untyped n 
  := unary (UntypedKind.inj b)
def Untyped.case: Untyped (n + 1) -> Untyped n -> Untyped n -> Untyped n -> Untyped n 
  := cases UntypedKind.case
def Untyped.elem: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.elem
def Untyped.let_set: Untyped (n + 2) -> Untyped n := 
  let_bin UntypedKind.let_set
def Untyped.lam_pr: Untyped n -> Untyped (n + 1) -> Untyped n
  := abs UntypedKind.lam_pr
def Untyped.app_pr: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.app_pr
def Untyped.lam_irrel: Untyped n -> Untyped (n + 1) -> Untyped n
  := abs UntypedKind.lam_irrel
def Untyped.app_irrel: Untyped n -> Untyped n -> Untyped n
  := bin UntypedKind.app_irrel
def Untyped.repr: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.repr
def Untyped.let_repr: Untyped (n + 2) -> Untyped n
  := let_bin UntypedKind.let_repr

-- Proofs
def Untyped.nil: Untyped n := const UntypedKind.nil
def Untyped.abort: Untyped n -> Untyped n := unary UntypedKind.abort
def Untyped.conj: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.conj
def Untyped.comp (b: Bool): Untyped n -> Untyped n 
  := unary (UntypedKind.comp b)
def Untyped.disj (b: Bool): Untyped n -> Untyped n 
  := unary (UntypedKind.disj b)
def Untyped.case_pr: Untyped (n + 1) -> Untyped n -> Untyped n -> Untyped n -> Untyped n 
  := cases UntypedKind.case_pr
def Untyped.imp: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.imp
def Untyped.mp: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.mp
def Untyped.general: Untyped n -> Untyped (n + 1) -> Untyped n
  := abs UntypedKind.general
def Untyped.inst: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.inst
def Untyped.witness: Untyped n -> Untyped n -> Untyped n 
  := bin UntypedKind.witness
def Untyped.let_wit: Untyped (n + 2) -> Untyped n
  := let_bin UntypedKind.let_wit
def Untyped.refl: Untyped n -> Untyped n := unary UntypedKind.refl