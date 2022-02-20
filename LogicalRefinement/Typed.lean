import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
open RawUntyped

inductive AnnotSort
  | type
  | prop

inductive Annot
  | sort (s: AnnotSort)
  | expr (s: AnnotSort) (A: RawUntyped)

def Annot.term := expr AnnotSort.type
def Annot.proof := expr AnnotSort.prop

open Annot
open AnnotSort

instance annotSortCoe: Coe AnnotSort Annot where
  coe := sort

@[simp]
def Annot.wk1: Annot -> Annot
  | sort s => sort s
  | expr s A => expr s (RawUntyped.wk1 A)

@[simp]
def Annot.lift1: Annot -> Annot
  | sort s => sort s
  | expr s A => expr s (RawUntyped.lift1 A)

@[simp]
def Annot.wk: Annot -> RawWk -> Annot
  | sort s, _ => sort s
  | expr s A, ρ => expr s (A.wk ρ)

@[simp]
def Annot.wk_composes: {A: Annot} -> (A.wk ρ).wk σ = A.wk (σ.comp ρ)
  | sort _ => rfl
  | expr _ _ => by simp

@[simp]
def Annot.wk_wk1: {A: Annot} -> (A.wk RawWk.wk1) = A.wk1
  | sort _ => rfl
  | expr _ _ => rfl

@[simp]
def Annot.wk_id {A: Annot}: A.wk RawWk.id = A := by {
  cases A; repeat simp
}

inductive HypKind
  | val (s: AnnotSort) -- Computational/Logical
  | gst -- Refinement

inductive HypKind.regular: HypKind -> AnnotSort -> Prop
  | val {s}: regular (val s) s
  | gst: regular gst type

@[simp]
def HypKind.upgrade: HypKind -> HypKind
  | val s => val s
  | gst => val type

@[simp]
theorem HypKind.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  cases h; repeat rfl
}

theorem HypKind.upgrade_regular {s} {h: HypKind} (p: h.regular s): 
  h.upgrade.regular s := by {
    cases s <;> cases h <;> cases p <;> constructor
  }

structure Hyp := (ty: RawUntyped) (kind: HypKind)

@[simp]
def Hyp.wk (H: Hyp) (ρ: RawWk) := Hyp.mk (H.ty.wk ρ) H.kind

@[simp]
def Hyp.subst (H: Hyp) (σ: RawSubst) := Hyp.mk (H.ty.subst σ) H.kind

@[simp]
def Hyp.annot: Hyp -> Annot
  | Hyp.mk ty (HypKind.val s) => Annot.expr s ty
  | Hyp.mk ty (HypKind.gst) => Annot.expr type ty

theorem Hyp.wk_components:
  Hyp.wk (Hyp.mk A h) ρ = Hyp.mk (A.wk ρ) h := rfl

@[simp]
def Hyp.upgrade (H: Hyp) := Hyp.mk H.ty H.kind.upgrade

@[simp]
theorem Hyp.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  simp only [upgrade, HypKind.upgrade_idem]
}

@[simp]
theorem Hyp.upgrade_wk_commute {h: Hyp}: 
  upgrade (h.wk ρ) = h.upgrade.wk ρ := by simp

def Hyp.val (A: RawUntyped) (s: AnnotSort) := Hyp.mk A (HypKind.val s)
def Hyp.gst (A: RawUntyped) := Hyp.mk A HypKind.gst

def Context := List Hyp

@[simp]
def Context.upgrade: Context -> Context
  | [] => []
  | h::hs => (h.upgrade)::(upgrade hs)

@[simp]
def Context.upgrade_length_is_length {Γ: Context}: Γ.upgrade.length = Γ.length := by {
  induction Γ with
  | nil => rfl
  | cons H Γ I => simp [I] 
}

@[simp]
theorem Context.upgrade_idem: upgrade (upgrade Γ) = upgrade Γ := by {
  induction Γ with
  | nil => rfl
  | cons A Γ I => 
    simp only [upgrade, Hyp.upgrade_idem]; 
    simp [I]
}

open RawUntyped

def RawUntyped.arrow (A B: RawUntyped) := pi A (wk1 B)

def constAnnot: UntypedKind [] -> Annot
  | UntypedKind.nats => type
  | UntypedKind.top => prop
  | UntypedKind.bot => prop
  | UntypedKind.zero => term nats
  | UntypedKind.succ => term (arrow nats nats)
  | UntypedKind.nil => proof top

inductive HasVar: Context -> RawUntyped -> AnnotSort -> Nat -> Prop
  | var0 {Γ: Context} {A: RawUntyped} {s: AnnotSort}:
    HasVar ((Hyp.mk A (HypKind.val s))::Γ) A.wk1 s 0
  | var_succ {Γ: Context} {A: RawUntyped} {s: AnnotSort} {H: Hyp} {n: Nat}:
    HasVar Γ A s n -> HasVar (H::Γ) A.wk1 s (n + 1)

theorem HasVar.fv: HasVar Γ A s n -> n < Γ.length := by {
  intros H;
  induction H with
  | var0 =>
    apply Nat.succ_le_succ
    apply Nat.zero_le
  | var_succ =>
    simp only [List.length]
    apply Nat.succ_le_succ
    assumption
}

inductive HasType: Context -> RawUntyped -> Annot -> Prop
  -- Variables
  | var {Γ: Context} {A: RawUntyped} {s: AnnotSort} {n: Nat}:
    HasType Γ A (sort s) ->
    HasVar Γ A s n ->
    HasType Γ (var n) (expr s A)

  -- Constants
  | nats {Γ}: HasType Γ nats type
  | top {Γ}: HasType Γ top prop
  | bot {Γ}: HasType Γ bot prop
  | zero {Γ}: HasType Γ zero (term nats)
  | succ {Γ}: HasType Γ succ (term (arrow nats nats))
  | nil {Γ}: HasType Γ nil (proof top)

  -- Basic types
  | pi {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: Context} {φ A: RawUntyped}:
    HasType Γ φ type  -> HasType Γ A type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (intersect A B) type
  | union {Γ: Context} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (union A B) type
  
  -- Basic propositions
  | and {Γ: Context} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (and φ ψ) prop
  | or {Γ: Context} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (or φ ψ) prop
  | implies {Γ: Context} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (implies φ ψ) prop
  | forall_ {Γ: Context} {A φ: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (forall_ A φ) type
  | exists_ {Γ: Context} {A φ: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (exists_ A φ) type
  | eq {Γ: Context} {A l r: RawUntyped}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (term A) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (eq A l r) prop

  -- Basic terms
  | lam {Γ: Context} {A s B: RawUntyped}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (term B) ->
    HasType Γ (lam A s) (term (pi A B))
  | app {Γ: Context} {A B l r: RawUntyped}:
    HasType Γ l (term (pi A B)) -> HasType Γ r (term A) ->
    HasType Γ (app l r) (term (B.subst0 l))
  | pair {Γ: Context} {A B l r: RawUntyped}:
    HasType Γ l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (pair l r) (term (sigma A B))
  | proj_ix {Γ: Context} {A B e: RawUntyped}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ (proj false e) (term A)
  | proj_dep {Γ: Context} {A B e: RawUntyped}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ (proj true e) (term (B.subst0 (proj false e)))
  | inj_l {Γ: Context} {A B e: RawUntyped}:
    HasType Γ e (term A) -> HasType Γ B type ->
    HasType Γ (inj false e) (term (coprod A B))
  | inj_r {Γ: Context} {A B e: RawUntyped}:
    HasType Γ e (term B) -> HasType Γ A type ->
    HasType Γ (inj true e) (term (coprod A B))
  
    --TODO: rest

  -- Basic proofs
  --TODO: this

notation Γ "⊢" a ":" A => HasType Γ a A
notation Γ "⊢" a "∈" A => HasType Γ a (term A)
notation Γ "⊢" a "∴" A => HasType Γ a (prop A)

theorem HasType.fv {Γ a A} (P: Γ ⊢ a: A): a.fv ≤ Γ.length := by {
  induction P 
  <;> intros 
  <;> try apply Nat.zero_le -- constants, e.g. nats, nil, zero
  case var =>
    apply HasVar.fv
    assumption
  all_goals (
    simp only [
      RawUntyped.fv, 
      Nat.max_r_le_split, 
      Nat.le_sub_is_le_add
    ];
    simp only [
      Context.upgrade_length_is_length
    ] at *
    repeat first | apply And.intro | assumption
  )
} 

theorem HasVar.upgrade (p: HasVar Γ A s n): HasVar Γ.upgrade A s n := by {
  induction p with
  | var0 => 
    simp only [Context.upgrade, Hyp.upgrade, HypKind.upgrade]
    exact var0
  | var_succ => apply var_succ; assumption
}

theorem HasType.upgrade (p: Γ ⊢ a: A): Γ.upgrade ⊢ a: A := by {
  induction p;
  case var => 
    apply var
    assumption
    apply HasVar.upgrade
    assumption
  all_goals { constructor; repeat assumption; }
}

--TODO: define context type, coercion to raw context?

inductive IsCtx: Context -> Prop
  | nil: IsCtx []
  | cons_val {Γ A s}: 
    IsCtx Γ -> (Γ ⊢ A: sort s) 
    -> IsCtx ((Hyp.mk A (HypKind.val s))::Γ)
  | cons_gst {Γ A}: 
    IsCtx Γ -> (Γ ⊢ A: type) -> 
    IsCtx ((Hyp.mk A HypKind.gst)::Γ)

-- theorem HasType.ctx_regular (p: Γ ⊢ a: A): IsCtx Γ := by {
--   induction p <;> first
--   | assumption
--   | constructor <;> assumption
-- }

inductive IsHyp: Context -> Hyp -> Prop
  | hyp_val {Γ A s}: (Γ ⊢ A: sort s) -> IsHyp Γ (Hyp.mk A (HypKind.val s))
  | hyp_gst {Γ A}: (Γ ⊢ A: type) -> IsHyp Γ (Hyp.mk A HypKind.gst)

-- def HasType.wk1
--   (Ha: HasType Γ a A) (H: Hyp) (HH: IsHyp Γ H):
--   HasType (H::Γ) a.wk1 A.wk1 := by { 
--     cases HH <;>
--     apply wk1_inner <;>
--     first | assumption | constructor
--   }

inductive WkCtx: RawWk -> Context -> Context -> Type
  | id: WkCtx RawWk.id [] []
  --TODO: make H explicit?
  | step {ρ Γ Δ H}: WkCtx ρ Γ Δ -> WkCtx ρ.step (H::Γ) Δ 
  | lift {ρ Γ Δ H}: WkCtx ρ Γ Δ -> WkCtx ρ.lift ((H.wk ρ)::Γ) (H::Δ)

theorem WkCtx.upgrade: WkCtx ρ Γ Δ 
  -> WkCtx ρ Γ.upgrade Δ.upgrade := by {
  intro R;
  induction R with
  | id => exact id
  | step R => apply step; assumption
  | lift R =>
    simp only [Context.upgrade, Hyp.upgrade_wk_commute]
    apply lift <;> assumption
}

theorem HasVar.wk:
  (ρ: RawWk) -> {Γ Δ: Context} -> (Hs: WkCtx ρ Γ Δ) ->
  {n: Nat} -> {A: RawUntyped} -> {s: AnnotSort} ->
  HasVar Δ A s n -> HasVar Γ (A.wk ρ) s (ρ.var n) 
  := by {
    intros ρ;
    induction ρ <;> intro Γ Δ R <;> cases R;
    case id => intros n A s H; cases H
    case step ρ I Γ H R =>
      intros n A s HΔ;
      simp only [RawUntyped.step_wk1]
      exact var_succ (I R HΔ)
    case lift ρ I Γ Δ H R =>
      intros n A s HΔ;
      cases HΔ with
      | var0 =>
        simp only [
          Wk.lift,
          RawUntyped.wk_composes,
          RawWk.var, RawUntyped.lift_wk1
        ]
        exact var0
      | var_succ =>
        simp only [
          Wk.lift,
          RawUntyped.wk_composes,
          RawWk.var, Nat.add, RawUntyped.lift_wk1
        ]
        apply var_succ
        apply I
        apply R
        assumption
  } 

theorem HasType.wk {Δ a A} (HΔ: Δ ⊢ a: A):
  {ρ: RawWk} -> {Γ: Context} -> WkCtx ρ Γ Δ ->
  (Γ ⊢ (a.wk ρ): (A.wk ρ)) := by {
    induction HΔ;
    case var I =>
      intros
      apply var
      apply I
      assumption
      apply HasVar.wk
      repeat assumption

    any_goals (
      intros ρ Γ R
      simp only [RawUntyped.wk, Annot.wk, term, RawUntyped.subst0_wk]
      constructor <;> (
        try rename_i I0 I1 I2
        simp only [Annot.wk, term, RawUntyped.subst0_wk] at *
        repeat ((first | apply I0 | apply I1 | apply I2) <;> 
          simp only [<-Hyp.wk_components] <;> 
          first 
          | (constructor; assumption) 
          | assumption 
          | (apply WkCtx.upgrade; assumption))
          )
      )
  }

--TODO: basic weakening helpers

-- def HasType.wk1_inner
--   (Ha: Γ ⊢ a: A) (HB: Γ ⊢ B: (sort s)) (Hr: h.regular s):
--   ((Hyp.mk B h)::Γ) ⊢ a.wk1: A.wk1 := by { 
--     induction Hr <;>
--     cases A <;>
--     constructor <;>
--     assumption
--   }

-- def HasType.wk_val (Ha: HasType Γ a A) (HB: HasType Γ B (sort s))
--   : HasType ((Hyp.val B s)::Γ) a.wk1 A.wk1
--   := wk1_inner Ha HB HypKind.regular.val

-- def HasType.wk_gst (Ha: HasType Γ a A) (HB: HasType Γ B type)
--   : HasType ((Hyp.gst B)::Γ) a.wk1 A.wk1
--   := wk1_inner Ha HB HypKind.regular.gst

--TODO: basic examples

-- -- Simple examples

-- def HasType.arrow (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type)
--   : Γ ⊢ (arrow A B): type 
--   := pi HA (wk_sort HB HA)

-- def HasType.lam_id (HA: Γ ⊢ A: type)
--   : Γ ⊢ (RawUntyped.lam A (var 0)) ∈ RawUntyped.arrow A A
--   := lam HA (var0 HA)

-- def HasType.const_lam 
--   (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type) (Hb: Γ ⊢ b ∈ B)
--   : HasType Γ (RawUntyped.lam A b.wk1) (term (RawUntyped.arrow A B))
--   := lam HA (wk_expr Hb HA)

--TODO: substitution lemma

def SubstCtx (σ: RawSubst) (Γ Δ: Context): Prop :=
  ∀{n}, (p: n < Δ.length) -> (Γ ⊢ σ n: (Δ.get ⟨n, p⟩).annot)

--TODO: basic substitution helpers, in particular for subst0. See HasType.regular

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
  induction p;

  all_goals try exact Annot.regular.sort

  case lam =>
    constructor; constructor <;>
    first | assumption | { apply Annot.regular_expr; assumption }

  --TODO: general tactic for app requires substitution lemma for subst0

  repeat sorry
}

theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }

theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }