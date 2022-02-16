import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
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
def Hyp.upgrade (H: Hyp) := Hyp.mk H.ty H.kind.upgrade

@[simp]
theorem Hyp.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  simp only [upgrade, HypKind.upgrade_idem]
}

def Hyp.val (A: RawUntyped) (s: AnnotSort) := Hyp.mk A (HypKind.val s)
def Hyp.gst (A: RawUntyped) := Hyp.mk A HypKind.gst

def Context := List Hyp

@[simp]
def Context.upgrade: Context -> Context
  | [] => []
  | h::hs => (h.upgrade)::(upgrade hs)

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

inductive HasType: Context -> RawUntyped -> Annot -> Prop
  -- Variables
  | var {Γ: Context} {A: RawUntyped} {s: AnnotSort} {n: Nat}:
    HasType Γ A (sort s) ->
    HasVar Γ A s n ->
    HasType ((Hyp.mk A (HypKind.val s))::Γ) (var n) (expr s A)

  -- Constants
  | nats: HasType [] nats type
  | top: HasType [] top prop
  | bot: HasType [] bot prop
  | zero: HasType [] zero (term nats)
  | succ: HasType [] succ (term (arrow nats nats))
  | nil: HasType [] nil (proof top)

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
    HasType Γ φ type  -> HasType Γ B type ->
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

-- structure Typed {Γ: Context} {A: Annot} :=
--   (val: RawUntyped) (p: Γ ⊢ val: A)

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

inductive IsCtx: Context -> Prop
  | nil: IsCtx []
  | cons_val {Γ A s}: 
    IsCtx Γ -> (Γ ⊢ A: sort s) 
    -> IsCtx ((Hyp.mk A (HypKind.val s))::Γ)
  | cons_gst {Γ A}: 
    IsCtx Γ -> (Γ ⊢ A: type) -> 
    IsCtx ((Hyp.mk A HypKind.gst)::Γ)

theorem HasType.ctx_regular (p: Γ ⊢ a: A): IsCtx Γ := by {
  induction p <;> first
  | assumption
  | constructor <;> assumption
}

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

inductive WkCtx: Context -> Context -> Type
  | id: WkCtx [] []
  --TODO: make H explicit?
  | step {Γ Δ H}: WkCtx Γ Δ -> IsHyp Γ H -> WkCtx (H::Γ) Δ 
  | lift {Γ Δ H}: WkCtx Γ Δ -> IsHyp Δ H -> WkCtx (H::Γ) (H::Δ)

def WkCtx.to_wk: WkCtx Γ Δ -> Wk Γ.length Δ.length
  | id => Wk.id
  | step ρ _ => Wk.step (to_wk ρ)
  | lift ρ _ => Wk.lift (to_wk ρ)

theorem HasVar.wk:
  {Γ Δ: Context} -> (ρ: WkCtx Γ Δ) ->
  {n: Nat} -> {A: RawUntyped} -> {s: AnnotSort} ->
  HasVar Δ A s n -> HasVar Γ (A.wk ρ.to_wk.val) s (ρ.to_wk.val.var n) 
  := by {
    intros Γ Δ ρ;
    induction ρ with
    | id => intros n A s H; cases H
    | step ρ H I =>
      intros n A s HΔ;
      simp only [WkCtx.to_wk, Wk.step, RawUntyped.step_wk1]
      exact var_succ (I HΔ)
    | lift =>
      intros n A s HΔ;
      cases HΔ with
      | var0 =>
        simp only [
          WkCtx.to_wk, Wk.lift,
          RawUntyped.wk_composes, RawUntyped.wk1,
          RawWk.var
        ]
        --TODO: lift wk1 is wk1 wk1
        sorry
      | var_succ =>
        simp only [
          WkCtx.to_wk, Wk.lift,
          RawUntyped.wk_composes, RawUntyped.wk1,
          RawWk.var, Nat.add
        ]
        --TODO: lift wk1 is wk1 wk1
        sorry
  } 

theorem HasType.wk: 
  {Γ Δ: Context} -> (ρ: WkCtx Γ Δ) ->
  {a: RawUntyped} ->
  {A: Annot} ->
  (Δ ⊢ a: A) ->
  (Γ ⊢ (a.wk ρ.to_wk.val): (A.wk ρ.to_wk.val)) := by {
    intro Γ;
    induction Γ with
    | nil =>
      intros Δ ρ;
      cases ρ;
      intros;
      simp only [
        Annot.wk_id, RawUntyped.wk_id, 
        WkCtx.to_wk, Wk.val, Wk.id]
      assumption
    | cons H Γ I =>
      intros Δ ρ;
      cases ρ with
      | step ρ HΓ => sorry
      | lift ρ HΔ => sorry
  }

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