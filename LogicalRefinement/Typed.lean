import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
open RawUntyped

inductive Annot
  | type
  | prop
  | term (A: RawUntyped)
  | proof (A: RawUntyped)

@[simp]
def Annot.wk1: Annot -> Annot
  | type => type
  | prop => prop
  | term A => term (RawUntyped.wk1 A)
  | proof A => proof (RawUntyped.wk1 A)

inductive Hyp
  | val (A: RawUntyped) -- Computational
  | ghost (A: RawUntyped) -- Refinement
  | log (A: RawUntyped) -- Logical

@[simp]
def Hyp.upgrade: Hyp -> Hyp
  | val A => val A
  | ghost A => val A
  | log A => log A

@[simp]
theorem Hyp.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  cases h; repeat rfl
}

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

open Annot
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
  -- | const0 {c: UntypedKind []}:
  --   HasType [] (const c) (constAnnot c)
  
  -- Weakening (TODO: condense to one rule?)
  | wk_val {Γ a A B}:
    HasType Γ a A -> HasType Γ B type 
    -> HasType ((Hyp.val B)::Γ) (wk1 a) (wk1 A)
  | wk_ghost {Γ a A B}:
    HasType Γ a A -> HasType Γ B type 
    -> HasType ((Hyp.ghost B)::Γ) (wk1 a) (wk1 A)
  | wk_log {Γ a A B}:
    HasType Γ a A -> HasType Γ B prop 
    -> HasType ((Hyp.log B)::Γ) (wk1 a) (wk1 A)

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
    HasType ((Hyp.val A)::Γ) s (term B) ->
    HasType Γ (lam A s) (term (pi A B))
  | app {Γ: RawContext} {A B l r: RawUntyped}:
    HasType Γ l (term (pi A B)) -> HasType Γ r (term A) ->
    HasType Γ (app l r) (term (B.subst0 l))
  -- | pair {Γ: RawContext} {A B l r: RawUntyped}:
  --   HasType Γ l (expr A) -> HasType Γ r (expr (B.subst0 l)) ->
  --   HasType Γ (pair l r) (expr (sigma A B))
  -- | proj_ix {Γ: RawContext} {A B e: RawUntyped}:
  --   HasType Γ e (expr (sigma A B)) ->
  --   HasType Γ (proj false e) (expr A)
  -- | proj_dep {Γ: RawContext} {A B e: RawUntyped}:
  --   HasType Γ e (expr (sigma A B)) ->
  --   HasType Γ (proj true e) (expr (B.subst0 (proj false e)))
  -- | inj_l {Γ: RawContext} {A B e: RawUntyped}:
  --   HasType Γ e (expr A) -> HasType Γ B type ->
  --   HasType Γ (inj false e) (expr (coprod A B))
  -- | inj_r {Γ: RawContext} {A B e: RawUntyped}:
  --   HasType Γ e (expr B) -> HasType Γ A type ->
  --   HasType Γ (inj true e) (expr (coprod A B))
  
    --TODO: rest

  -- Basic proofs
  --TODO: this

-- Simple examples

def HasType.wk_val_ty: HasType Γ a type -> HasType Γ B type 
    -> HasType ((Hyp.val B)::Γ) (wk1 a) type := wk_val

def HasType.wk_val_expr: HasType Γ a (term A) -> HasType Γ B type 
    -> HasType ((Hyp.val B)::Γ) (wk1 a) (term (wk1 A)) := wk_val

def HasType.arrow (HA: HasType Γ A type) (HB: HasType Γ B type)
  : HasType Γ (arrow A B) type 
  := pi HA (wk_val HB HA)

def HasType.lam_id (HA: HasType Γ A type)
  : HasType Γ (RawUntyped.lam A (var 0)) (term (RawUntyped.arrow A A)) 
  := lam (var0_val HA)

def HasType.const_lam 
  (HA: HasType Γ A type) (HB: HasType Γ B type) (Hb: HasType Γ b (term B))
  : HasType Γ (RawUntyped.lam A (wk1 b)) (term (RawUntyped.arrow A B))
  := lam (wk_val Hb HA)

theorem HasType.upgrade (p: HasType Γ a A): HasType Γ.upgrade a A := by {
  induction p;
  
  case wk_ghost IA IB => exact wk_val IA IB

  case var0_val IA => exact var0_val IA
  case var0_log IA => exact var0_log IA
  --case const0 => exact const0
  
  case wk_val Ia IB => exact wk_val Ia IB
  case wk_log Ia IB => exact wk_log Ia IB
  
  case pi IA IB => exact pi IA IB
  case sigma IA IB => exact sigma IA IB
  case coprod IA IB => exact coprod IA IB
  case set IA IB => exact set IA IB
  case assume Iφ IA => exact assume Iφ IA
  case intersect IA IB => exact intersect IA IB
  case union IA IB => exact union IA IB

  case and Iφ Iψ => exact and Iφ Iψ
  case or Iφ Iψ => exact or Iφ Iψ
  case implies Iφ Iψ => exact implies Iφ Iψ
  case forall_ IA Iφ => exact forall_ IA Iφ
  case exists_ IA Iφ => exact exists_ IA Iφ
  case eq IA Il Ir => exact eq IA Il Ir

  case lam Ib => exact lam Ib
  case app Il Ir => exact app Il Ir
}

theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
  := by {
    cases p;

  }

theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
  := sorry