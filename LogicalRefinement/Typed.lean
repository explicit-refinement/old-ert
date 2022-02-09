import LogicalRefinement.Untyped
open RawUntyped

def RawContext := List RawUntyped

inductive HasType: RawContext -> RawUntyped -> RawUntyped -> Prop
  | var0 {Γ: RawContext} {A: RawUntyped}: HasType (A::Γ) (var 0) A

  | wk {Γ: RawContext} {t: RawUntyped} {A: RawUntyped} (_: HasType Γ t A) (B: RawUntyped)
  : HasType (B::Γ) (wk1 t) (wk1 A)