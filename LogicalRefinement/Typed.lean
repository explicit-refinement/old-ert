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

inductive RawPath: RawContext -> RawUntyped -> RawUntyped -> Annot -> Prop
  -- Variables
  | var {Γ: RawContext} {n: Nat} {A: RawUntyped}:
    Γ.get? n = some (Hyp.mk A true) ->
    RawPath Γ (var n) (var n) (expr (wkn n A))
  
  -- Constants
  | const {Γ: RawContext} {c: UntypedKind []}:
    RawPath Γ (const c) (const c) (constAnnot c)

theorem RawPath.upgrade (p: RawPath Γ a b A): RawPath Γ.upgrade a b A := by {
  induction p with
  | const => exact const
  | _ => sorry
}

inductive IsContext: RawContext -> Prop
  | nil: IsContext []
  | cons_typ (Γ: RawContext) (A: RawUntyped) (comp: Bool):
    RawPath Γ A A type -> IsContext Γ -> IsContext ((Hyp.mk A comp)::Γ)
  | cons_prop (Γ: RawContext) (A: RawUntyped):
    RawPath Γ A A type -> IsContext Γ -> IsContext ((Hyp.mk A true)::Γ)

structure Context := (val: RawContext) (p: IsContext val)

--TODO: think about this
structure Path (Γ: Context) (l r: RawUntyped) (A: Annot) :=
  (val: RawPath Γ.val l r A)

def HasAnnot (Γ: Context) (a: RawUntyped) (A: Annot) := Path Γ a a A

def IsType (Γ: Context) (A: RawUntyped) := Path Γ A A type

def IsProp (Γ: Context) (A: RawUntyped) := Path Γ A A prop

def HasType (Γ: Context) (a: RawUntyped) (A: RawUntyped) := 
  Path Γ a a (expr A)