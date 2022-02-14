import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
open RawUntyped

inductive AnnotSort
  | type
  | prop

inductive Annot
  | sort (s: AnnotSort)
  | term (A: RawUntyped)
  | proof (A: RawUntyped)

open Annot
open AnnotSort

instance annotSortCoe: Coe AnnotSort Annot where
  coe := sort

@[simp]
def Annot.wk1: Annot -> Annot
  | sort s => sort s
  | term A => term (RawUntyped.wk1 A)
  | proof A => proof (RawUntyped.wk1 A)

@[simp]
def Annot.wk: Annot -> RawWk -> Annot
  | sort s, _ => sort s
  | term A, ρ => term (A.wk ρ)
  | proof A, ρ => proof (A.wk ρ)

@[simp]
def Annot.wk_id {A: Annot}: A.wk RawWk.id = A := by {
  cases A; repeat simp
}

inductive HypKind
  | val -- Computational
  | gst -- Refinement
  | log -- Logical

inductive HypKind.regular: HypKind -> AnnotSort -> Prop
  | val: regular val type
  | gst : regular gst type
  | log: regular log prop

@[simp]
def HypKind.upgrade: HypKind -> HypKind
  | val => val
  | gst => val
  | log => log

@[simp]
theorem HypKind.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  cases h; repeat rfl
}

theorem HypKind.upgrade_regular {s} {h: HypKind} (p: h.regular s): 
  h.upgrade.regular s := by {
    cases s <;> cases h <;> { first | constructor | contradiction }
  }

structure Hyp := (ty: RawUntyped) (kind: HypKind)

@[simp]
def Hyp.upgrade (H: Hyp) := Hyp.mk H.ty H.kind.upgrade

@[simp]
theorem Hyp.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  simp only [upgrade, HypKind.upgrade_idem]
}

def Hyp.val (A: RawUntyped) := Hyp.mk A HypKind.val
def Hyp.gst (A: RawUntyped) := Hyp.mk A HypKind.gst
def Hyp.log (A: RawUntyped) := Hyp.mk A HypKind.log

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
  | var0_val {Γ: RawContext} {A: RawUntyped}:
    HasType Γ A type ->
    HasType ((Hyp.val A)::Γ) (var 0) (term (wk1 A))
  | var0_log {Γ: RawContext} {A: RawUntyped}:
    HasType Γ A prop ->
    HasType ((Hyp.log A)::Γ) (var 0) (proof (wk1 A))

  -- Constants
  | nats: HasType [] nats type
  | top: HasType [] top prop
  | bot: HasType [] bot prop
  | zero: HasType [] zero (term nats)
  | succ: HasType [] succ (term (arrow nats nats))
  | nil: HasType [] nil (proof top)
  
  -- Weakening (TODO: condense to one rule?)
  | wk1 {Γ a A B s h}:
    HasType Γ a A -> 
    HasType Γ B (sort s) ->
    h.regular s ->
    HasType ((Hyp.mk B h)::Γ) a.wk1 A.wk1

  -- Basic types
  | pi {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: RawContext} {φ A: RawUntyped}:
    HasType Γ φ type  -> HasType Γ B type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) B prop ->
    HasType Γ (intersect A B) type
  | union {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) B prop ->
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
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) φ prop ->
    HasType Γ (forall_ A φ) type
  | exists_ {Γ: RawContext} {A φ: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val A)::Γ) φ prop ->
    HasType Γ (exists_ A φ) type
  | eq {Γ: RawContext} {A l r: RawUntyped}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (term A) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (eq A l r) prop

  -- Basic terms
  | lam {Γ: RawContext} {A s B: RawUntyped}:
    HasType Γ A type ->
    HasType ((Hyp.val A)::Γ) s (term B) ->
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

def HasType.wk_val (Ha: HasType Γ a A) (HB: HasType Γ B type)
  : HasType ((Hyp.val B)::Γ) a.wk1 A.wk1
  := wk1 Ha HB HypKind.regular.val

def HasType.wk_gst (Ha: HasType Γ a A) (HB: HasType Γ B type)
  : HasType ((Hyp.gst B)::Γ) a.wk1 A.wk1
  := wk1 Ha HB HypKind.regular.gst

def HasType.wk_log (Ha: HasType Γ a A) (HB: HasType Γ B prop)
  : HasType ((Hyp.log B)::Γ) a.wk1 A.wk1
  := wk1 Ha HB HypKind.regular.log

notation Γ "⊢" a ":" A => HasType Γ a A
notation Γ "⊢" a "∈" A => HasType Γ a (term A)
notation Γ "⊢" a "∴" A => HasType Γ a (prop A)

-- Simple examples

def HasType.arrow (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type)
  : Γ ⊢ (arrow A B): type 
  := pi HA (wk_val HB HA)

def HasType.lam_id (HA: Γ ⊢ A: type)
  : Γ ⊢ (RawUntyped.lam A (var 0)) ∈ RawUntyped.arrow A A
  := lam HA (var0_val HA)

def HasType.const_lam 
  (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type) (Hb: Γ ⊢ b ∈ B)
  : HasType Γ (RawUntyped.lam A b.wk1) (term (RawUntyped.arrow A B))
  := lam HA (wk_val Hb HA)

theorem HasType.upgrade (p: Γ ⊢ a: A): Γ.upgrade ⊢ a: A := by {
  induction p;
  case wk1 Ia IB =>
    simp only [RawContext.upgrade, Hyp.upgrade]
    apply wk1 Ia IB
    apply HypKind.upgrade_regular
    assumption
  all_goals { constructor; repeat assumption; }
}

inductive Annot.regular: Annot -> RawContext -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | term {Γ A}: (Γ ⊢ A: type) -> regular (term A) Γ
  | proof {Γ A}: (Γ ⊢ A: prop) -> regular (proof A) Γ

theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
  induction p;
  repeat sorry
}

theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
  := by {
    let H := regular p;
    cases H with
    | term H => exact H
  }

theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
  := by {
    let H := regular p;
    cases H with
    | proof H => exact H
  }

inductive IsCtx: RawContext -> Prop
  | nil: IsCtx []
  | cons_val {Γ A}: IsCtx Γ -> (Γ ⊢ A: type) -> IsCtx ((Hyp.val A)::Γ)
  | cons_gst {Γ A}: IsCtx Γ -> (Γ ⊢ A: type) -> IsCtx ((Hyp.gst A)::Γ)
  | cons_log {Γ A}: IsCtx Γ -> (Γ ⊢ A: prop) -> IsCtx ((Hyp.log A)::Γ)

theorem HasType.ctx_regular (p: Γ ⊢ a: A): IsCtx Γ := by {
  induction p;

  -- Handle constants
  all_goals try exact IsCtx.nil

  -- Variables
  case var0_val HA IA => exact IsCtx.cons_val IA HA
  case var0_log HA IA => exact IsCtx.cons_log IA HA

  repeat sorry
}

inductive IsHyp: RawContext -> Hyp -> Prop
  | hyp_val {Γ A}: (Γ ⊢ A: type) -> IsHyp Γ (Hyp.val A)
  | hyp_gst {Γ A}: (Γ ⊢ A: type) -> IsHyp Γ (Hyp.gst A)
  | hyp_log {Γ A}: (Γ ⊢ A: prop) -> IsHyp Γ (Hyp.log A)

inductive WkCtx: RawContext -> RawContext -> Type
  | id: WkCtx [] []
  --TODO: make H explicit?
  | step {Γ Δ H}: WkCtx Γ Δ -> IsHyp Γ H -> WkCtx (H::Γ) Δ 
  | lift {Γ Δ H}: WkCtx Γ Δ -> WkCtx (H::Γ) (H::Δ)

def WkCtx.to_wk: WkCtx Γ Δ -> Wk Γ.length Δ.length
  | id => Wk.id
  | step ρ _ => Wk.step (to_wk ρ)
  | lift ρ => Wk.lift (to_wk ρ)

-- TODO: swap RawUntyped.wk
theorem HasType.wk (ρ: WkCtx Γ Δ) (H: Γ ⊢ a: A): 
  Δ ⊢ (a.wk ρ.to_wk.val): (A.wk ρ.to_wk.val) := by {
    induction ρ with
    | id =>
      simp only [WkCtx.to_wk]
      --TODO: this should be a simp lemma...
      let H': ∀ n, (@Wk.id n).val = RawWk.id := λn => rfl;
      rw [H']
      rw [RawUntyped.wk_id, Annot.wk_id]
      exact H
    | step => sorry
    | lift => sorry
  }

-- TODO: hastype untyped method?