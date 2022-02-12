import LogicalRefinement.Untyped
open RawUntyped

inductive Annot
  | type
  | prop
  | expr (A: RawUntyped)

def RawContext := List RawUntyped

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
  | var {Γ: RawContext} {n: Nat} (p: n < Γ.length):
    RawPath Γ (var n) (var n) (expr (wkn n (Γ.get n p)))
  
  -- Constants
  | const {Γ: RawContext} {c: UntypedKind []}:
    RawPath Γ (const c) (const c) (constAnnot c)

def IsAnnot (Γ: RawContext) (A: RawUntyped) :=  
  RawPath Γ A A type ∨ RawPath Γ A A prop

inductive IsContext: RawContext -> Prop
  | nil: IsContext []
  | cons (Γ: RawContext) (A: RawUntyped):
    IsAnnot Γ A -> IsContext Γ -> IsContext (A::Γ)

structure Context := (val: RawContext) (p: IsContext val)

--TODO: think about this
structure Path (Γ: Context) (l r: RawUntyped) (A: Annot) :=
  (val: RawPath Γ.val l r A)

def HasAnnot (Γ: Context) (a: RawUntyped) (A: Annot) := Path Γ a a A

def IsType (Γ: Context) (A: RawUntyped) := Path Γ A A type

def IsProp (Γ: Context) (A: RawUntyped) := Path Γ A A prop

def HasType (Γ: Context) (a: RawUntyped) (A: RawUntyped) := 
  Path Γ a a (expr A)