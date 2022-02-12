import LogicalRefinement.Untyped
open RawUntyped

inductive Annot
  | type
  | prop
  | expr (A: RawUntyped)

structure Hyp := (annot: RawUntyped) (comp: Bool)

def Hyp.upgrade (h: Hyp): Hyp := Hyp.mk (h.annot) true

def RawContext := List Hyp

def RawContext.upgrade: RawContext -> RawContext
  | [] => []
  | h::hs => (h.upgrade)::hs

open Annot
open RawUntyped

def constAnnot: UntypedKind [] -> Annot
  | UntypedKind.nats => type
  | UntypedKind.top => prop
  | UntypedKind.bot => prop
  | UntypedKind.nat _ => expr nats
  | UntypedKind.nil => expr top

inductive RawHasType: RawContext -> RawUntyped -> Annot -> Prop
  -- Variables
  | var {Γ: RawContext} {n: Nat} {A: RawUntyped}:
    Γ.get? n = some (Hyp.mk A true) ->
    RawHasType Γ (var n) (expr (wkn n A))
  
  -- Constants
  | const {Γ: RawContext} {c: UntypedKind []}:
    RawHasType Γ (const c) (constAnnot c)

  -- Basic types
  | pi {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A true)::Γ) B type ->
    RawHasType Γ (pi A B) type
  | sigma {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A true)::Γ) B type ->
    RawHasType Γ (sigma A B) type
  | coprod {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType Γ B type ->
    RawHasType Γ (coprod A B) type
  | set {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A true)::Γ) B prop ->
    RawHasType Γ (set A B) type
  | assume {Γ: RawContext} {φ A: RawUntyped}:
    RawHasType Γ φ type  -> RawHasType Γ B type ->
    RawHasType Γ (assume φ A) type
  | intersect {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A false)::Γ) B prop ->
    RawHasType Γ (intersect A B) type
  | union {Γ: RawContext} {A B: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A false)::Γ) B prop ->
    RawHasType Γ (union A B) type
  
  -- Basic propositions
  | and {Γ: RawContext} {φ ψ: RawUntyped}:
    RawHasType Γ φ prop -> RawHasType Γ ψ prop ->
    RawHasType Γ (and φ ψ) prop
  | or {Γ: RawContext} {φ ψ: RawUntyped}:
    RawHasType Γ φ prop -> RawHasType Γ ψ prop ->
    RawHasType Γ (or φ ψ) prop
  | implies {Γ: RawContext} {φ ψ: RawUntyped}:
    RawHasType Γ φ prop -> RawHasType Γ ψ prop ->
    RawHasType Γ (implies φ ψ) prop
  | forall_ {Γ: RawContext} {A φ: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A false)::Γ) φ prop ->
    RawHasType Γ (forall_ A φ) type
  | exists_ {Γ: RawContext} {A φ: RawUntyped}:
    RawHasType Γ A type -> RawHasType ((Hyp.mk A false)::Γ) φ prop ->
    RawHasType Γ (exists_ A φ) type
  | eq {Γ: RawContext} {A l r: RawUntyped}:
    RawHasType Γ A type -> 
    RawHasType Γ.upgrade l (expr A) -> RawHasType Γ.upgrade r (expr A) ->
    RawHasType Γ (eq A l r) prop

  -- Basic terms
  --TODO: this

  -- Basic proofs
  --TODO: this

theorem RawHasType.upgrade (p: RawHasType Γ a A): RawHasType Γ.upgrade a A := by {
  induction p with
  | const => exact const
  | _ => sorry
}

inductive IsContext: RawContext -> Prop
  | nil: IsContext []
  | cons_typ (Γ: RawContext) (A: RawUntyped) (comp: Bool):
    RawHasType Γ A type -> IsContext Γ -> IsContext ((Hyp.mk A comp)::Γ)
  | cons_prop (Γ: RawContext) (A: RawUntyped):
    RawHasType Γ A type -> IsContext Γ -> IsContext ((Hyp.mk A true)::Γ)

structure Context := (val: RawContext) (p: IsContext val)

--TODO: think about this
def HasType (Γ: Context) (a: RawUntyped) (A: Annot) := RawHasType Γ.val a A