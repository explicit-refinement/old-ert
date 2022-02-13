import LogicalRefinement.Untyped
open RawUntyped

inductive Annot
  | type
  | prop
  | expr (A: RawUntyped)

@[simp]
def Annot.wk1: Annot -> Annot
  | type => type
  | prop => prop
  | expr A => expr (RawUntyped.wk1 A)

inductive Hyp
  | val (A: RawUntyped)
  | ghost (A: RawUntyped)

@[simp]
def Hyp.upgrade: Hyp -> Hyp
  | val A => val A
  | ghost A => val A

def RawContext := List Hyp

@[simp]
def RawContext.upgrade: RawContext -> RawContext
  | [] => []
  | h::hs => (h.upgrade)::hs

open Annot
open RawUntyped

def constAnnot: UntypedKind [] -> Annot
  | UntypedKind.nats => type
  | UntypedKind.top => prop
  | UntypedKind.bot => prop
  | UntypedKind.zero => expr nats
  | UntypedKind.nil => expr top

inductive HasType: RawContext -> RawUntyped -> Annot -> Prop
  -- Variables
  | var0 {Γ: RawContext} {A: RawUntyped}:
    HasType Γ A type ->
    HasType ((Hyp.val A)::Γ) (var 0) (expr A)

  -- Constants
  | const0 {c: UntypedKind []}:
    HasType [] (const c) (constAnnot c)
  
  -- Weakening
  | wk_val {Γ a A B}:
    HasType Γ a A -> HasType Γ B type 
    -> HasType ((Hyp.val B)::Γ) (wk1 a) (wk1 A)
  | wk_ghost {Γ a A B}:
    HasType Γ a A -> HasType Γ B type 
    -> HasType ((Hyp.ghost B)::Γ) (wk1 a) (wk1 A)
  | wk_prop {Γ a A B}:
    HasType Γ a A -> HasType Γ B prop 
    -> HasType ((Hyp.val B)::Γ) (wk1 a) (wk1 A)

  -- Basic types
  | pi {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: RawContext} {φ A: RawUntyped}:
    HasType Γ φ type  -> HasType Γ B type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) B prop ->
    HasType Γ (intersect A B) type
  | union {Γ: RawContext} {A B: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) B prop ->
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
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) φ prop ->
    HasType Γ (forall_ A φ) type
  | exists_ {Γ: RawContext} {A φ: RawUntyped}:
    HasType Γ A type -> HasType ((Hyp.val (wk1 A))::Γ) φ prop ->
    HasType Γ (exists_ A φ) type
  | eq {Γ: RawContext} {A l r: RawUntyped}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (expr A) -> HasType Γ.upgrade r (expr A) ->
    HasType Γ (eq A l r) prop

  -- Basic terms
  | lam {Γ: RawContext} {A s B: RawUntyped}:
    HasType ((Hyp.val (wk1 A))::Γ) s (expr B) ->
    HasType Γ (lam A s) (expr (pi A B))

  -- Basic proofs
  --TODO: this

def RawUntyped.arrow (A: RawUntyped) := pi A (wk1 A)

theorem HasType.upgrade (p: HasType Γ a A): HasType Γ.upgrade a A := by {
  induction p;
  repeat sorry
}