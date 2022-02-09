import LogicalRefinement.Untyped

def RawContext := List RawUntyped

inductive HasType: RawContext -> RawUntyped -> RawUntyped -> Prop
  | var0 (Γ: RawContext) (A: RawUntyped): HasType (A::Γ) (RawUntyped.var 0) A

  | wk (Γ: RawContext) (t: RawUntyped) (A B: RawUntyped) (_: HasType Γ t A)
  : HasType (B::Γ) (RawUntyped.wk1 t) (RawUntyped.wk1 A)