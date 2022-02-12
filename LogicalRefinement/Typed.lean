import LogicalRefinement.Untyped
open RawUntyped

inductive RawType
  | type
  | prop
  | expr (A: RawUntyped)

def RawContext := List RawUntyped

open RawType
open RawUntyped

inductive Path: RawContext -> RawUntyped -> RawUntyped -> RawType -> Prop
  | var {Γ: RawContext} {n: Nat} (p: n < Γ.length):
    Path Γ (var n) (var n) (expr (Γ.get n p))

def IsType (Γ: RawContext) (A: RawUntyped) := Path Γ A A type

def IsProp (Γ: RawContext) (A: RawUntyped) := Path Γ A A prop

def HasType (Γ: RawContext) (a: RawUntyped) (A: RawUntyped) := Path Γ a a (expr A)