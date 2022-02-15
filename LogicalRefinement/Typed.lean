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
def Annot.wk: Annot -> RawWk -> Annot
  | sort s, _ => sort s
  | expr s A, ρ => expr s (A.wk ρ)

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

def RawContext := List Hyp

@[simp]
def RawContext.upgrade: RawContext -> RawContext
  | [] => []
  | h::hs => (h.upgrade)::(upgrade hs)

@[simp]
theorem RawContext.upgrade_idem: upgrade (upgrade Γ) = upgrade Γ := by {
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

inductive HasType: RawContext -> RawUntyped -> Annot -> Prop
  -- Variables
  | var0 {Γ: RawContext} {A: RawUntyped} {s: AnnotSort}:
    HasType Γ A (sort s) ->
    HasType ((Hyp.val A s)::Γ) (var 0) (expr s (wk1 A))

  -- Constants
  | nats: HasType [] nats type
  | top: HasType [] top prop
  | bot: HasType [] bot prop
  | zero: HasType [] zero (term nats)
  | succ: HasType [] succ (term (arrow nats nats))
  | nil: HasType [] nil (proof top)
  
  -- Weakening
  | wk_sort {Γ A B s s'}:
    HasType Γ A (sort s) -> 
    HasType Γ B (sort s') ->
    HasType ((Hyp.mk B (HypKind.val s'))::Γ) A.wk1 (sort s)
  | wk_gst_sort {Γ A B s}:
    HasType Γ A (sort s) -> 
    HasType Γ B type ->
    HasType ((Hyp.mk B HypKind.gst)::Γ) A.wk1 (sort s)
  | wk_expr {Γ a A B s s'}:
    HasType Γ a (expr s A) -> 
    HasType Γ B (sort s') ->
    HasType ((Hyp.mk B (HypKind.val s'))::Γ) a.wk1 (expr s A.wk1)
  | wk_gst_expr {Γ a A B s}:
    HasType Γ a (expr s A) -> 
    HasType Γ B type ->
    HasType ((Hyp.mk B HypKind.gst)::Γ) a.wk1 (expr s A.wk1)

  -- Basic types
  | pi {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: RawContext} {φ A: RawUntyped}:
    HasType Γ φ type  -> HasType Γ B type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (intersect A B) type
  | union {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (union A B) type
  
  -- Basic propositions
  | and {Γ: RawContext} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (and φ ψ) prop
  | or {Γ: RawContext} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (or φ ψ) prop
  | implies {Γ: RawContext} {φ ψ: RawUntyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (implies φ ψ) prop
  | forall_ {Γ: RawContext} {A φ: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (forall_ A φ) type
  | exists_ {Γ: RawContext} {A φ: RawUntyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (exists_ A φ) type
  | eq {Γ: RawContext} {A l r: RawUntyped}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (term A) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (eq A l r) prop

  -- Basic terms
  | lam {Γ: RawContext} {A s B: RawUntyped}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (term B) ->
    HasType Γ (lam A s) (term (pi A B))
  | app {Γ: RawContext} {A B l r: RawUntyped}:
    HasType Γ l (term (pi A B)) -> HasType Γ r (term A) ->
    HasType Γ (app l r) (term (B.subst0 l))
  | pair {Γ: RawContext} {A B l r: RawUntyped}:
    HasType Γ l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (pair l r) (term (sigma A B))
  | proj_ix {Γ: RawContext} {A B e: RawUntyped}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ (proj false e) (term A)
  | proj_dep {Γ: RawContext} {A B e: RawUntyped}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ (proj true e) (term (B.subst0 (proj false e)))
  | inj_l {Γ: RawContext} {A B e: RawUntyped}:
    HasType Γ e (term A) -> HasType Γ B type ->
    HasType Γ (inj false e) (term (coprod A B))
  | inj_r {Γ: RawContext} {A B e: RawUntyped}:
    HasType Γ e (term B) -> HasType Γ A type ->
    HasType Γ (inj true e) (term (coprod A B))
  
    --TODO: rest

  -- Basic proofs
  --TODO: this

def HasType.wk1 
  (Ha: HasType Γ a A) (HB: HasType Γ B (sort s)) (Hr: h.regular s):
  HasType ((Hyp.mk B h)::Γ) a.wk1 A.wk1 := by { sorry }

def HasType.wk_val (Ha: HasType Γ a A) (HB: HasType Γ B (sort s))
  : HasType ((Hyp.val B s)::Γ) a.wk1 A.wk1
  := wk1 Ha HB HypKind.regular.val

def HasType.wk_gst (Ha: HasType Γ a A) (HB: HasType Γ B type)
  : HasType ((Hyp.gst B)::Γ) a.wk1 A.wk1
  := wk1 Ha HB HypKind.regular.gst

notation Γ "⊢" a ":" A => HasType Γ a A
notation Γ "⊢" a "∈" A => HasType Γ a (term A)
notation Γ "⊢" a "∴" A => HasType Γ a (prop A)

structure Typed {Γ: RawContext} {A: Annot} :=
  (val: RawUntyped) (p: Γ ⊢ val: A)

-- Simple examples

def HasType.arrow (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type)
  : Γ ⊢ (arrow A B): type 
  := pi HA (wk_sort HB HA)

def HasType.lam_id (HA: Γ ⊢ A: type)
  : Γ ⊢ (RawUntyped.lam A (var 0)) ∈ RawUntyped.arrow A A
  := lam HA (var0 HA)

def HasType.const_lam 
  (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type) (Hb: Γ ⊢ b ∈ B)
  : HasType Γ (RawUntyped.lam A b.wk1) (term (RawUntyped.arrow A B))
  := lam HA (wk_expr Hb HA)

theorem HasType.upgrade (p: Γ ⊢ a: A): Γ.upgrade ⊢ a: A := by {
  induction p;
  all_goals { constructor; repeat assumption; }
}

inductive IsCtx: RawContext -> Prop
  | nil: IsCtx []
  | cons_val {Γ A s}: 
    IsCtx Γ -> (Γ ⊢ A: sort s) 
    -> IsCtx ((Hyp.mk A (HypKind.val s))::Γ)
  | cons_gst {Γ A}: 
    IsCtx Γ -> (Γ ⊢ A: type) -> 
    IsCtx ((Hyp.mk A HypKind.gst)::Γ)

theorem HasType.ctx_regular (p: Γ ⊢ a: A): IsCtx Γ := by {
  induction p;

  -- Handle constants
  all_goals try exact IsCtx.nil

  repeat sorry
}

inductive IsHyp: RawContext -> Hyp -> Prop
  | hyp_val {Γ A s}: (Γ ⊢ A: type) -> IsHyp Γ (Hyp.val A s)
  | hyp_gst {Γ A}: (Γ ⊢ A: type) -> IsHyp Γ (Hyp.gst A)

inductive WkCtx: RawContext -> RawContext -> Type
  | id: WkCtx [] []
  --TODO: make H explicit?
  | step {Γ Δ H}: WkCtx Γ Δ -> IsHyp Γ H -> WkCtx (H::Γ) Δ 
  | lift {Γ Δ H}: WkCtx Γ Δ -> WkCtx (H::Γ) (H::Δ)

def WkCtx.to_wk: WkCtx Γ Δ -> Wk Γ.length Δ.length
  | id => Wk.id
  | step ρ _ => Wk.step (to_wk ρ)
  | lift ρ => Wk.lift (to_wk ρ)

theorem HasType.var_wk (ρ: WkCtx Γ Δ) (D: Γ ⊢ RawUntyped.var v: A):
  (Γ ⊢ var (ρ.to_wk.val.var v): A) := sorry

-- TODO: swap RawUntyped.wk
theorem HasType.wk (ρ: WkCtx Γ Δ) (D: Γ ⊢ a: A): 
  Δ ⊢ (a.wk ρ.to_wk.val): (A.wk ρ.to_wk.val) := by {
    induction ρ with
    | id =>
      simp only [WkCtx.to_wk]
      --TODO: this should be a simp lemma...
      let H': ∀ n, (@Wk.id n).val = RawWk.id := λn => rfl;
      rw [H']
      rw [RawUntyped.wk_id, Annot.wk_id]
      exact D
    | step => sorry
    | lift => sorry
  }

inductive Annot.regular: Annot -> RawContext -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
  induction p;

  all_goals try exact Annot.regular.sort

  case var0 =>
    constructor ;
    constructor <;>
    assumption
  case lam =>
    constructor; constructor <;>
    first | assumption | { apply Annot.regular_expr; assumption }
  case app => sorry


  -- Need substitution for the rest...
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